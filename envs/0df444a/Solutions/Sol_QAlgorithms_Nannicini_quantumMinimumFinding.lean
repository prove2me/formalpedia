-- Prove2me | solution 1 for QAlgorithms.Nannicini.quantumMinimumFinding
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:57:46.288791+00:00
-- url     : https://prove2.me/submissions/2b005b36-870a-4b68-87f9-2b9238180a21

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Definitions.Def_QAlgorithms_Nannicini_Ch04c_Model
import Theorems.Thm_QAlgorithms_Nannicini_quantumSearch_unknownCount
import Theorems.Thm_QAlgorithms_Nannicini_quantumSearch_unknownCount_sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option maxHeartbeats 800000

open QAlgorithms
open QAlgorithms.Nannicini
open scoped ENNReal Matrix

namespace SolQuantumMinimumFinding

/-! ## Section 1: Gate and Query Bounds on the Support of `minFindWeight` -/

private lemma two_mul_add_mul_le_four_mul_pow (m : ℕ) :
    2 * m + m * (m + 1) ≤ 4 * 2 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | _ | m
    · omega
    · omega
    · have hpow : m + 1 + 1 < 2 ^ (m + 1 + 1) := Nat.lt_two_pow_self
      have h1 : 2 * (m + 1 + 1 + 1) + (m + 1 + 1 + 1) * (m + 1 + 1 + 1 + 1) =
          (2 * (m + 1 + 1) + (m + 1 + 1) * (m + 1 + 1 + 1)) + (2 * m + 8) := by ring
      have h2 : 4 * 2 ^ (m + 1 + 1 + 1) = 4 * 2 ^ (m + 1 + 1) + 4 * 2 ^ (m + 1 + 1) := by ring
      have h3 : 2 ^ 2 ≤ 2 ^ (m + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega

private lemma mfRoundOverhead_le_two_mul_pow (m : ℕ) :
    mfRoundOverhead m ≤ 2 * 2 ^ m := by
  unfold mfRoundOverhead
  have h := two_mul_add_mul_le_four_mul_pow m
  omega

private def ChainLe (a : ℕ) : List ℕ → ℕ → Prop
  | [], d => d ≤ a
  | m :: rest, d => m ≤ a ∧ ChainLe (m + 1) rest d

private lemma ChainLe.mono {a a' : ℕ} {L : List ℕ} {d : ℕ}
    (h : a ≤ a') (hL : ChainLe a L d) : ChainLe a' L d := by
  cases L with
  | nil => exact le_trans hL h
  | cons m rest => exact ⟨le_trans hL.1 h, hL.2⟩

private lemma ChainLe.append {a b d : ℕ} {L₁ L₂ : List ℕ}
    (h₁ : ChainLe a L₁ b) (h₂ : ChainLe b L₂ d) : ChainLe a (L₁ ++ L₂) d := by
  induction L₁ generalizing a with
  | nil => exact h₂.mono h₁
  | cons m rest ih => exact ⟨h₁.1, ih h₁.2⟩

private lemma chainLe_range_flatMap (k : ℕ) :
    ChainLe 1 ((List.range k).flatMap fun i => [i + 1, i + 1]) (k + 1) := by
  induction k with
  | zero => simp [ChainLe]
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append]
    refine ih.append ?_
    simp [ChainLe]

private lemma chainLe_alg1RoundList (n : ℕ) :
    ChainLe 1 (alg1RoundList n) n := by
  unfold alg1RoundList
  have h := chainLe_range_flatMap (n - 1)
  induction h_gen : (List.range (n - 1)).flatMap (fun i => [i + 1, i + 1]) generalizing n with
  | nil =>
    rw [h_gen] at h
    change n - 1 + 1 ≤ 1 at h
    change n ≤ 1
    omega
  | cons m rest _ =>
    -- Use general monotonicity on the final target d:
    exact (by
      have h_d : ∀ {a d' d : ℕ} {L : List ℕ}, d ≤ d' → ChainLe a L d' → ChainLe a L d := by
        intro a d' d L hdd' hL
        induction L generalizing a with
        | nil => exact le_trans hdd' hL
        | cons x xs ihx => exact ⟨hL.1, ihx hL.2⟩
      rw [← h_gen]
      exact h_d (by omega : n ≤ (n - 1) + 1) h)

private lemma alg1Gates_zero (n b : ℕ) (L : List ℕ) :
    alg1Gates n b L 0 = 0 := by
  cases L <;> rfl

private lemma alg1Gates_le_of_chainLe (n b : ℕ) (L : List ℕ) (m₀ d c : ℕ)
    (hL : ChainLe m₀ L d) :
    alg1Gates n b L c ≤ c * (mfStepGates n b + 6) + if c = 0 then 0 else 2 * 2 ^ m₀ := by
  induction L generalizing m₀ c with
  | nil =>
    by_cases hc : c = 0
    · subst hc; simp [alg1Gates_zero]
    · simp only [alg1Gates, if_neg hc]
      have : c * mfStepGates n b ≤ c * (mfStepGates n b + 6) :=
        Nat.mul_le_mul_left c (by omega)
      omega
  | cons m rest ih =>
    by_cases hc : c = 0
    · subst hc; simp [alg1Gates_zero]
    · obtain ⟨hm, hrest⟩ := hL
      have hpow : 2 ^ m ≤ 2 ^ m₀ := Nat.pow_le_pow_right (by omega) hm
      have hov : mfRoundOverhead m ≤ 2 * 2 ^ m := mfRoundOverhead_le_two_mul_pow m
      rcases Nat.exists_eq_succ_of_ne_zero hc with ⟨c', rfl⟩
      rw [if_neg (Nat.succ_ne_zero c')]
      change (if c' + 1 ≤ 2 ^ m then mfRoundOverhead m + (c' + 1) * mfStepGates n b
        else mfRoundOverhead m + 2 ^ m * mfStepGates n b + alg1Gates n b rest (c' + 1 - 2 ^ m)) ≤
        (c' + 1) * (mfStepGates n b + 6) + 2 * 2 ^ m₀
      split_ifs with hle
      · have h1 : (c' + 1) * mfStepGates n b ≤ (c' + 1) * (mfStepGates n b + 6) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      · have hsub_ne : c' + 1 - 2 ^ m ≠ 0 := by omega
        have ih_step := ih (m + 1) (c' + 1 - 2 ^ m) hrest
        rw [if_neg hsub_ne] at ih_step
        have hpow_succ : 2 * 2 ^ (m + 1) = 4 * 2 ^ m := by ring
        have h_split : 2 ^ m * mfStepGates n b + (c' + 1 - 2 ^ m) * (mfStepGates n b + 6) +
            6 * 2 ^ m = (c' + 1) * (mfStepGates n b + 6) := by
          have h_add : 2 ^ m + (c' + 1 - 2 ^ m) = c' + 1 := by omega
          calc 2 ^ m * mfStepGates n b + (c' + 1 - 2 ^ m) * (mfStepGates n b + 6) + 6 * 2 ^ m
              = 2 ^ m * (mfStepGates n b + 6) + (c' + 1 - 2 ^ m) * (mfStepGates n b + 6) := by ring
            _ = (2 ^ m + (c' + 1 - 2 ^ m)) * (mfStepGates n b + 6) := by rw [← Nat.add_mul]
            _ = (c' + 1) * (mfStepGates n b + 6) := by rw [h_add]
        omega

private lemma mfStepGates_pos (n b : ℕ) : 1 ≤ mfStepGates n b := by
  unfold mfStepGates; omega

private lemma alg1Gates_alg1RoundList_le (n b c : ℕ) :
    alg1Gates n b (alg1RoundList n) c ≤ 11 * c * mfStepGates n b := by
  have h := alg1Gates_le_of_chainLe n b (alg1RoundList n) 1 n c (chainLe_alg1RoundList n)
  have hstep := mfStepGates_pos n b
  by_cases hc : c = 0
  · subst hc; simp [alg1Gates_zero]
  · rw [if_neg hc] at h
    have hc1 : 1 ≤ c := Nat.pos_of_ne_zero hc
    have h_prod : 1 ≤ c * mfStepGates n b := Nat.mul_pos hc1 hstep
    have h_step6 : c * (mfStepGates n b + 6) ≤ 7 * (c * mfStepGates n b) := by
      calc c * (mfStepGates n b + 6)
          = c * mfStepGates n b + 6 * (c * 1) := by ring
        _ ≤ c * mfStepGates n b + 6 * (c * mfStepGates n b) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left c hstep)) _
        _ = 7 * (c * mfStepGates n b) := by ring
    have h_11 : 7 * (c * mfStepGates n b) + 4 * (c * mfStepGates n b) =
        11 * c * mfStepGates n b := by ring
    omega

private lemma searchAlg1Enum_cost_gt {n : ℕ} (g : Qubits n → Bool) (c : ℕ)
    (oc : Option (Qubits n) × ℕ) (h : searchAlg1Enum g c oc ≠ 0) :
    c + 1 ≤ oc.2 := by
  unfold searchAlg1Enum at h
  by_cases hex : ∃ j, g j = true
  · rw [if_pos hex] at h
    by_cases hmin : ∃ j, g j = true ∧ (∀ j', g j' = true → bitsToNat j ≤ bitsToNat j') ∧
        oc = (some j, c + bitsToNat j + 1)
    · rcases hmin with ⟨j, _, _, rfl⟩
      dsimp
      omega
    · rw [if_neg hmin] at h
      exact absurd rfl h
  · rw [if_neg hex] at h
    by_cases hnone : oc = (none, c + 2 ^ n)
    · subst hnone
      dsimp
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    · rw [if_neg hnone] at h
      exact absurd rfl h

private lemma searchAlg1Rounds_cost_gt {n : ℕ} (g : Qubits n → Bool) (rounds : List ℕ)
    (c : ℕ) (oc : Option (Qubits n) × ℕ) (h : searchAlg1Rounds g rounds c oc ≠ 0) :
    c + 1 ≤ oc.2 := by
  induction rounds generalizing c with
  | nil => exact searchAlg1Enum_cost_gt g c oc h
  | cons m rest ih =>
    simp only [searchAlg1Rounds] at h
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h_rhs : (if g j = true then if oc = (some j, c + (2 ^ m - 1 + 1)) then (1 : ℝ≥0∞) else 0
        else searchAlg1Rounds g rest (c + (2 ^ m - 1 + 1)) oc) ≠ 0 :=
      right_ne_zero_of_mul hj
    by_cases hgj : g j = true
    · rw [if_pos hgj] at h_rhs
      by_cases hoc : oc = (some j, c + (2 ^ m - 1 + 1))
      · subst hoc; dsimp; omega
      · rw [if_neg hoc] at h_rhs; exact absurd rfl h_rhs
    · rw [if_neg hgj] at h_rhs
      have := ih (c + (2 ^ m - 1 + 1)) h_rhs
      omega

private lemma searchAlg1Weight_cost_pos {n : ℕ} (g : Qubits n → Bool)
    (oc : Option (Qubits n) × ℕ) (h : searchAlg1Weight g oc ≠ 0) :
    1 ≤ oc.2 :=
  searchAlg1Rounds_cost_gt g (alg1RoundList n) 0 oc h

private lemma minFindLoop_support_bounds {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (fuel : ℕ) (l : Qubits n) (q g : ℕ) (out : Qubits n × ℕ × ℕ)
    (hq : q ≤ T) (h : minFindLoop f b T fuel l q g out ≠ 0) :
    q ≤ out.2.1 ∧ out.2.1 ≤ T ∧ out.2.2 ≤ g + 12 * (out.2.1 - q) * mfStepGates n b := by
  induction fuel generalizing l q g with
  | zero =>
    simp only [minFindLoop] at h
    by_cases hout : out = (l, q, g)
    · subst hout
      refine ⟨le_refl q, hq, by simp⟩
    · rw [if_neg hout] at h
      exact absurd rfl h
  | succ fuel ih =>
    simp only [minFindLoop] at h
    have ⟨oc, hoc⟩ : ∃ oc, searchAlg1Weight (fun j => decide (f j < f l)) oc *
        (if q + oc.2 ≤ T then
          minFindLoop f b T fuel
            (match oc.1 with
              | some k => if f k < f l then k else l
              | none => l)
            (q + oc.2) (g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b) out
        else if out = (l, T, g + alg1Gates n b (alg1RoundList n) (T - q)) then 1 else 0) ≠ 0 := by
      by_contra h_none
      apply h
      rw [ENNReal.tsum_eq_zero]
      intro oc
      exact Classical.not_not.mp fun hne => h_none ⟨oc, hne⟩
    have hw : searchAlg1Weight (fun j => decide (f j < f l)) oc ≠ 0 := left_ne_zero_of_mul hoc
    have hbr := right_ne_zero_of_mul hoc
    have hoc_pos : 1 ≤ oc.2 := searchAlg1Weight_cost_pos _ oc hw
    by_cases hqT : q + oc.2 ≤ T
    · rw [if_pos hqT] at hbr
      obtain ⟨h1, h2, h3⟩ := ih _ (q + oc.2)
        (g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b) hqT hbr
      refine ⟨by omega, h2, ?_⟩
      have hgates := alg1Gates_alg1RoundList_le n b oc.2
      have h12 : alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b ≤
          12 * oc.2 * mfStepGates n b := by
        calc alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b
            ≤ 11 * oc.2 * mfStepGates n b + 1 * mfStepGates n b := by omega
          _ ≤ 11 * oc.2 * mfStepGates n b + oc.2 * mfStepGates n b :=
              Nat.add_le_add_left (Nat.mul_le_mul_right _ hoc_pos) _
          _ = 12 * oc.2 * mfStepGates n b := by ring
      have h_sub : oc.2 + (out.2.1 - (q + oc.2)) = out.2.1 - q := by omega
      calc out.2.2
          ≤ g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b +
              12 * (out.2.1 - (q + oc.2)) * mfStepGates n b := h3
        _ ≤ g + 12 * oc.2 * mfStepGates n b + 12 * (out.2.1 - (q + oc.2)) * mfStepGates n b := by omega
        _ = g + 12 * (oc.2 + (out.2.1 - (q + oc.2))) * mfStepGates n b := by ring
        _ = g + 12 * (out.2.1 - q) * mfStepGates n b := by rw [h_sub]
    · rw [if_neg hqT] at hbr
      by_cases hout : out = (l, T, g + alg1Gates n b (alg1RoundList n) (T - q))
      · subst hout
        dsimp
        have hgates := alg1Gates_alg1RoundList_le n b (T - q)
        refine ⟨hq, le_refl T, ?_⟩
        calc g + alg1Gates n b (alg1RoundList n) (T - q)
            ≤ g + 11 * (T - q) * mfStepGates n b := by omega
          _ ≤ g + 12 * (T - q) * mfStepGates n b := by
              refine Nat.add_le_add_left ?_ g
              exact Nat.mul_le_mul_right _ (by omega)
      · rw [if_neg hout] at hbr
        exact absurd rfl hbr

private lemma minFindWeight_support_bounds {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (out : Qubits n × ℕ × ℕ) (h : minFindWeight f b T out ≠ 0) :
    out.2.1 ≤ T ∧ out.2.2 ≤ 12 * T * mfStepGates n b := by
  unfold minFindWeight at h
  obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hloop := right_ne_zero_of_mul hl
  obtain ⟨_, h2, h3⟩ := minFindLoop_support_bounds f b T (T + 1) l 0 0 out (Nat.zero_le T) hloop
  simp only [Nat.sub_zero, Nat.zero_add] at h3
  exact ⟨h2, le_trans h3 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 h2))⟩

/-! ## Section 2: Symmetry of `aeState` and Decomposition of `searchAlg1Rounds` -/

private def boolSign (b : Bool) : ℂ := if b then -1 else 1

private lemma bool_add_false_false : (false + false : Bool) = false := rfl
private lemma bool_add_false_true : (false + true : Bool) = true := rfl
private lemma bool_add_true_false : (true + false : Bool) = true := rfl
private lemma bool_add_true_true : (true + true : Bool) = false := rfl

private lemma boolSign_add (a b : Bool) : boolSign (a + b) = boolSign a * boolSign b := by
  cases a <;> cases b <;>
    simp [bool_add_false_false, bool_add_false_true, bool_add_true_false, bool_add_true_true,
      boolSign]

private lemma boolSign_sum {α : Type*} (s : Finset α) (f : α → Bool) :
    boolSign (∑ x ∈ s, f x) = ∏ x ∈ s, boolSign (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, boolSign_add, ih, Finset.prod_insert ha]

private lemma sum_boolSign_dotBits (n : ℕ) (j l : Qubits n) :
    (∑ i : Qubits n, boolSign (dotBits i j) * boolSign (dotBits l i)) =
      if j = l then (2 : ℂ) ^ n else 0 := by
  have h1 : (∑ i : Qubits n, boolSign (dotBits i j) * boolSign (dotBits l i)) =
      ∑ i : Qubits n, ∏ k : Fin n, (boolSign (i k && j k) * boolSign (l k && i k)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotBits, dotBits, boolSign_sum, boolSign_sum, ← Finset.prod_mul_distrib]
  rw [h1, ← Fintype.prod_sum (fun (k : Fin n) (b : Bool) =>
    boolSign (b && j k) * boolSign (l k && b))]
  have h2 : ∀ k : Fin n,
      (∑ b : Bool, boolSign (b && j k) * boolSign (l k && b)) =
        if j k = l k then (2 : ℂ) else 0 := by
    intro k
    cases j k <;> cases l k <;> (simp [boolSign]; try ring)
  simp_rw [h2]
  by_cases hjl : j = l
  · subst hjl; simp [Finset.prod_const]
  · rw [if_neg hjl]
    have ⟨k, hk⟩ : ∃ k : Fin n, j k ≠ l k := Function.ne_iff.mp hjl
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

private lemma hadamardN_apply_eq (n : ℕ) (j i : Qubits n) :
    hadamardN n j i = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * boolSign (dotBits i j) := by
  simp only [hadamardN, Matrix.of_apply, boolSign]
  split_ifs <;> ring

private lemma hadamardN_mul_hadamardN (n : ℕ) :
    hadamardN n * hadamardN n = 1 := by
  ext j l
  simp only [Matrix.mul_apply, hadamardN_apply_eq, Matrix.one_apply]
  have h_pull : (∑ i : Qubits n,
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * boolSign (dotBits i j) *
        ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * boolSign (dotBits l i))) =
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)) *
        ∑ i : Qubits n, boolSign (dotBits i j) * boolSign (dotBits l i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h_pull, sum_boolSign_dotBits]
  split_ifs with hjl
  · have h2 : ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)) *
        (2 : ℂ) ^ n = (((((Real.sqrt 2)⁻¹ ^ 2) * 2 : ℝ) ^ n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2]
    have hsqrt : (Real.sqrt 2)⁻¹ ^ 2 * 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [hsqrt, one_pow, Complex.ofReal_one]
  · ring

private lemma bool_zero_eq_false : (0 : Bool) = false := rfl

private lemma dotBits_zero_left (n : ℕ) (j : Qubits n) :
    dotBits (0 : Qubits n) j = false := by
  unfold dotBits
  have h : ∀ x : Fin n, ((0 : Qubits n) x && j x) = (0 : Bool) := fun _ => rfl
  simp_rw [h]
  exact Finset.sum_const_zero

private lemma dotBits_zero_right (n : ℕ) (j : Qubits n) :
    dotBits j (0 : Qubits n) = false := by
  unfold dotBits
  have h : ∀ x : Fin n, (j x && (0 : Qubits n) x) = (0 : Bool) := fun x => Bool.and_false (j x)
  simp_rw [h]
  exact Finset.sum_const_zero

private lemma hadamardN_zero_col (n : ℕ) (j : Qubits n) :
    hadamardN n j (0 : Qubits n) = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := by
  rw [hadamardN_apply_eq, dotBits_zero_left, boolSign]
  simp

private lemma zeroKet_eq_ket_zero (n : ℕ) : zeroKet n = ket (0 : Qubits n) := rfl

private lemma act_hadamardN_zeroKet_eq (n : ℕ) (j₁ j₂ : Qubits n) :
    act (hadamardN n) (zeroKet n) j₁ = act (hadamardN n) (zeroKet n) j₂ := by
  have h : ∀ j : Qubits n, act (hadamardN n) (zeroKet n) j = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := by
    intro j
    rw [zeroKet_eq_ket_zero]
    simp only [act, ket, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp,
      PiLp.single_apply]
    rw [Finset.sum_eq_single (0 : Qubits n)]
    · simp [hadamardN_zero_col]
    · intro i _ hi
      rw [if_neg hi, mul_zero]
    · simp
  rw [h j₁, h j₂]

private lemma hadamardN_reflAt_hadamardN_apply (n : ℕ) (j l : Qubits n) :
    (hadamardN n * reflAt (0 : Qubits n) * hadamardN n) j l =
      2 * (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * hadamardN n (0 : Qubits n) l -
        (1 : Matrix (Qubits n) (Qubits n) ℂ) j l := by
  rw [← hadamardN_mul_hadamardN n, ← hadamardN_zero_col n j]
  simp only [Matrix.mul_apply, reflAt, Matrix.diagonal_apply]
  have h_lhs : (∑ i : Qubits n,
      (∑ k : Qubits n, hadamardN n j k * if k = i then if k = 0 then (1 : ℂ) else -1 else 0) *
        hadamardN n i l) =
      ∑ i : Qubits n, ((if i = 0 then 2 * hadamardN n j 0 * hadamardN n 0 l else 0) -
        hadamardN n j i * hadamardN n i l) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg hk, mul_zero]) (by simp)]
    by_cases hi : i = 0
    · subst hi; simp; ring
    · rw [if_pos rfl, if_neg hi, if_neg hi]; ring
  rw [h_lhs, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (0 : Qubits n)]
  simp

private lemma act_mul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

private lemma act_ampAmpIterate_eq_of_eq {n : ℕ} (g : Qubits n → Bool)
    (v : EuclideanSpace ℂ (Qubits n)) (j₁ j₂ : Qubits n)
    (hgj : g j₁ = g j₂) (hv : v j₁ = v j₂) :
    act (ampAmpIterate (hadamardN n) (phaseOracle g) 0) v j₁ =
      act (ampAmpIterate (hadamardN n) (phaseOracle g) 0) v j₂ := by
  have h_iter : ampAmpIterate (hadamardN n) (phaseOracle g) 0 =
      (hadamardN n * reflAt (0 : Qubits n) * hadamardN n) * phaseOracle g := by
    simp [ampAmpIterate, hadamardN_star]
  rw [h_iter, act_mul_matrix]
  set w := act (phaseOracle g) v
  have hw : ∀ j, w j = (if g j then -1 else 1) * v j := by
    intro j
    simp [w, act, phaseOracle, Matrix.mulVec_diagonal]
  have hw_eq : w j₁ = w j₂ := by rw [hw j₁, hw j₂, hgj, hv]
  have h_act : ∀ j, act (hadamardN n * reflAt (0 : Qubits n) * hadamardN n) w j =
      (∑ l : Qubits n, 2 * (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * hadamardN n (0 : Qubits n) l * w l) -
        w j := by
    intro j
    simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp,
      hadamardN_reflAt_hadamardN_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp [ite_mul, one_mul, zero_mul]
  rw [h_act j₁, h_act j₂, hw_eq]

private lemma act_ampAmpIterate_pow_eq_of_eq {n : ℕ} (g : Qubits n → Bool) (k : ℕ)
    (j₁ j₂ : Qubits n) (hgj : g j₁ = g j₂) :
    act (ampAmpIterate (hadamardN n) (phaseOracle g) 0 ^ k) (act (hadamardN n) (zeroKet n)) j₁ =
      act (ampAmpIterate (hadamardN n) (phaseOracle g) 0 ^ k) (act (hadamardN n) (zeroKet n)) j₂ := by
  induction k with
  | zero =>
    simp only [pow_zero, act, Matrix.one_mulVec]
    exact act_hadamardN_zeroKet_eq n j₁ j₂
  | succ k ih =>
    rw [pow_succ', act_mul_matrix]
    exact act_ampAmpIterate_eq_of_eq g _ j₁ j₂ hgj ih

private lemma act_kronecker_one_apply {m n : ℕ} (A : Matrix (Qubits m) (Qubits m) ℂ)
    (v : EuclideanSpace ℂ (Qubits m × Qubits n)) (b : Qubits m) (j : Qubits n) :
    act (Matrix.kronecker A (1 : Matrix (Qubits n) (Qubits n) ℂ)) v (b, j) =
      ∑ b₁ : Qubits m, A b b₁ * v (b₁, j) := by
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    have : ¬ (j = j') := Ne.symm hj'
    simp [this]
  · simp

private lemma controlledPower_apply {κ : Type*} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (U : Matrix κ κ ℂ) (p q : Qubits m × κ) :
    controlledPower m U p q = if p.1 = q.1 then (U ^ bitsToNat p.1) p.2 q.2 else 0 := rfl

private lemma act_controlledPower_kronecker_apply {m n : ℕ}
    (U : Matrix (Qubits n) (Qubits n) ℂ) (A : Matrix (Qubits m) (Qubits m) ℂ)
    (φ : EuclideanSpace ℂ (Qubits m)) (ψ : EuclideanSpace ℂ (Qubits n))
    (b₁ : Qubits m) (j : Qubits n) :
    act (controlledPower m U)
      (act (Matrix.kronecker A (1 : Matrix (Qubits n) (Qubits n) ℂ)) (tensorVec φ ψ)) (b₁, j) =
      (∑ b₀ : Qubits m, A b₁ b₀ * φ b₀) * act (U ^ bitsToNat b₁) ψ j := by
  generalize hv_def :
    act (Matrix.kronecker A (1 : Matrix (Qubits n) (Qubits n) ℂ)) (tensorVec φ ψ) = v
  have hv : ∀ x : Qubits n, v (b₁, x) = (∑ b₀ : Qubits m, A b₁ b₀ * φ b₀) * ψ x := by
    intro x
    rw [← hv_def, act_kronecker_one_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b₀ _ => ?_
    simp only [tensorVec, WithLp.ofLp_toLp]
    ring
  simp only [act, controlledPower_apply, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b₁]
  · simp only [↓reduceIte]
    have hv' : ∀ x : Qubits n, v.ofLp (b₁, x) = (∑ b₀ : Qubits m, A b₁ b₀ * φ.ofLp b₀) * ψ.ofLp x :=
      hv
    simp_rw [hv']
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  · intro b' _ hb'
    have : ¬ (b₁ = b') := Ne.symm hb'
    simp [this]
  · simp

private lemma phaseEstimationState_eq_of_eq {m n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (ψ : EuclideanSpace ℂ (Qubits n)) (j₁ j₂ : Qubits n)
    (hU : ∀ k : ℕ, act (U ^ k) ψ j₁ = act (U ^ k) ψ j₂) (b : Qubits m) :
    phaseEstimationState m U ψ (b, j₁) = phaseEstimationState m U ψ (b, j₂) := by
  unfold phaseEstimationState
  rw [act_mul_matrix, act_mul_matrix, act_kronecker_one_apply, act_kronecker_one_apply]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [act_controlledPower_kronecker_apply, act_controlledPower_kronecker_apply, hU (bitsToNat b₁)]

private lemma aeState_eq_of_eq {m n : ℕ} (g : Qubits n → Bool) (j₁ j₂ : Qubits n)
    (hgj : g j₁ = g j₂) (b : Qubits m) :
    aeState m (hadamardN n) (phaseOracle g) (b, j₁) =
      aeState m (hadamardN n) (phaseOracle g) (b, j₂) :=
  phaseEstimationState_eq_of_eq _ _ j₁ j₂ (fun k => act_ampAmpIterate_pow_eq_of_eq g k j₁ j₂ hgj) b

private noncomputable def aeRoundProb {n : ℕ} (g : Qubits n → Bool) (m : ℕ) (j : Qubits n) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ b : Qubits m, prob (aeState m (hadamardN n) (phaseOracle g)) (b, j))

private lemma aeRoundProb_eq_of_eq {n : ℕ} (g : Qubits n → Bool) (m : ℕ) (j₁ j₂ : Qubits n)
    (hgj : g j₁ = g j₂) :
    aeRoundProb g m j₁ = aeRoundProb g m j₂ := by
  unfold aeRoundProb
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [prob, ket, EuclideanSpace.inner_single_left, one_mul, starRingEnd_apply, star_one,
    aeState_eq_of_eq g j₁ j₂ hgj b]

private noncomputable def searchAlg1Quant {n : ℕ} (g : Qubits n → Bool) :
    List ℕ → ℕ → Option (Qubits n) × ℕ → ℝ≥0∞
  | [], _, _ => 0
  | m :: rest, c, oc =>
      ∑ j : Qubits n,
        aeRoundProb g m j *
          (if g j = true then (if oc = (some j, c + ((2 ^ m - 1) + 1)) then 1 else 0)
          else searchAlg1Quant g rest (c + ((2 ^ m - 1) + 1)) oc)

private noncomputable def searchAlg1FailProb {n : ℕ} (g : Qubits n → Bool) : List ℕ → ℝ≥0∞
  | [] => 1
  | m :: rest =>
      (∑ j : Qubits n, if g j = true then 0 else aeRoundProb g m j) *
        searchAlg1FailProb g rest

private def roundsCost : List ℕ → ℕ
  | [] => 0
  | m :: rest => ((2 ^ m - 1) + 1) + roundsCost rest

private lemma searchAlg1Rounds_eq_quant_add_enum {n : ℕ} (g : Qubits n → Bool)
    (rounds : List ℕ) (c : ℕ) (oc : Option (Qubits n) × ℕ) :
    searchAlg1Rounds g rounds c oc =
      searchAlg1Quant g rounds c oc +
        searchAlg1FailProb g rounds * searchAlg1Enum g (c + roundsCost rounds) oc := by
  induction rounds generalizing c with
  | nil =>
    simp [searchAlg1Rounds, searchAlg1Quant, searchAlg1FailProb, roundsCost]
  | cons m rest ih =>
    simp only [searchAlg1Rounds, searchAlg1Quant, searchAlg1FailProb, roundsCost]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    change aeRoundProb g m j * _ = _
    by_cases hgj : g j = true
    · rw [if_pos hgj, if_pos hgj, if_pos hgj, zero_mul, zero_mul, add_zero]
    · rw [if_neg hgj, if_neg hgj, if_neg hgj, ih (c + (2 ^ m - 1 + 1)), mul_add, ← mul_assoc,
        Nat.add_assoc c (2 ^ m - 1 + 1) (roundsCost rest)]

private lemma searchAlg1Quant_eq_zero_of_not_marked {n : ℕ} (g : Qubits n → Bool)
    (rounds : List ℕ) (c : ℕ) (oc : Option (Qubits n) × ℕ)
    (h : ∀ j, oc.1 = some j → g j = false) :
    searchAlg1Quant g rounds c oc = 0 := by
  induction rounds generalizing c with
  | nil => rfl
  | cons m rest ih =>
    simp only [searchAlg1Quant]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hgj : g j = true
    · have hoc : oc ≠ (some j, c + (2 ^ m - 1 + 1)) := by
        intro heq
        have := h j (by rw [heq])
        rw [hgj] at this
        contradiction
      simp [hgj, hoc]
    · simp [hgj, ih (c + (2 ^ m - 1 + 1))]

private lemma searchAlg1Quant_some_eq_of_marked {n : ℕ} (g : Qubits n → Bool)
    (rounds : List ℕ) (c c' : ℕ) (j₁ j₂ : Qubits n)
    (hj₁ : g j₁ = true) (hj₂ : g j₂ = true) :
    searchAlg1Quant g rounds c (some j₁, c') = searchAlg1Quant g rounds c (some j₂, c') := by
  induction rounds generalizing c with
  | nil => rfl
  | cons m rest ih =>
    simp only [searchAlg1Quant]
    let swapEquiv : Qubits n ≃ Qubits n := Equiv.swap j₁ j₂
    rw [← swapEquiv.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hgj : g (swapEquiv j) = g j := by
      dsimp [swapEquiv]
      by_cases h1 : j = j₁
      · subst h1; simp [hj₁, hj₂]
      · by_cases h2 : j = j₂
        · subst h2; simp [hj₁, hj₂]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    have hprob : aeRoundProb g m (swapEquiv j) = aeRoundProb g m j :=
      aeRoundProb_eq_of_eq g m (swapEquiv j) j hgj
    rw [hprob, hgj]
    by_cases hgj_true : g j = true
    · rw [if_pos hgj_true, if_pos hgj_true]
      have hj_iff : (some j₁, c') = (some (swapEquiv j), c + (2 ^ m - 1 + 1)) ↔
          (some j₂, c') = (some j, c + (2 ^ m - 1 + 1)) := by
        simp only [Prod.mk.injEq, Option.some.injEq, and_congr_left_iff]
        intro _
        dsimp [swapEquiv]
        constructor <;> intro h
        · have := congr_arg (Equiv.swap j₁ j₂) h
          simpa using this
        · subst h; simp
      by_cases h_cond : (some j₂, c') = (some j, c + (2 ^ m - 1 + 1))
      · rw [if_pos (hj_iff.mpr h_cond), if_pos h_cond]
      · rw [if_neg (mt hj_iff.mp h_cond), if_neg h_cond]
    · rw [if_neg hgj_true, if_neg hgj_true]
      exact congr_arg (aeRoundProb g m j * ·) (ih (c + (2 ^ m - 1 + 1)))

private lemma roundsCost_append (L₁ L₂ : List ℕ) :
    roundsCost (L₁ ++ L₂) = roundsCost L₁ + roundsCost L₂ := by
  induction L₁ with
  | nil => simp [roundsCost]
  | cons m rest ih =>
    simp only [List.cons_append, roundsCost, ih]
    omega

private lemma two_pow_le_roundsCost_alg1RoundList (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n ≤ roundsCost (alg1RoundList n) := by
  unfold alg1RoundList
  obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
  rw [hk, List.range_succ, List.flatMap_append, roundsCost_append]
  have h_last : roundsCost [k + 1, k + 1] = 2 ^ (k + 2) := by
    simp only [roundsCost]
    have : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := Nat.sub_add_cancel Nat.one_le_two_pow
    have h2 : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    omega
  have hkn : k + 2 = n := by omega
  rw [List.flatMap_singleton, h_last, hkn]
  omega

private lemma searchAlg1Enum_tsum_eq_one_of_marked {n : ℕ} (g : Qubits n → Bool) (c : ℕ)
    (h_ex : ∃ j, g j = true) :
    (∑' oc : Option (Qubits n) × ℕ, searchAlg1Enum g c oc) = 1 ∧
      ∀ oc, searchAlg1Enum g c oc ≠ 0 → c ≤ oc.2 := by
  classical
  have h_nonempty : ((Finset.univ.filter fun j => g j = true).image bitsToNat).Nonempty := by
    rcases h_ex with ⟨j, hj⟩
    exact ⟨bitsToNat j, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩⟩
  let m_min := ((Finset.univ.filter fun j => g j = true).image bitsToNat).min' h_nonempty
  have hm_mem := Finset.min'_mem ((Finset.univ.filter fun j => g j = true).image bitsToNat) h_nonempty
  rcases Finset.mem_image.mp hm_mem with ⟨j₀, hj₀_mem, hj₀_eq⟩
  have hj₀_true : g j₀ = true := (Finset.mem_filter.mp hj₀_mem).2
  have hj₀_min : ∀ j', g j' = true → bitsToNat j₀ ≤ bitsToNat j' := by
    intro j' hj'
    rw [hj₀_eq]
    exact Finset.min'_le _ (bitsToNat j')
      (Finset.mem_image.mpr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ j', hj'⟩, rfl⟩)
  have h_inj : Function.Injective (bitsToNat (n := n)) := by
    intro x y hxy
    apply (bitsEquivFin n).injective
    apply Fin.ext
    rw [bitsEquivFin_apply, bitsEquivFin_apply, hxy]
  have h_enum_eq : ∀ oc : Option (Qubits n) × ℕ,
      searchAlg1Enum g c oc = if oc = (some j₀, c + bitsToNat j₀ + 1) then 1 else 0 := by
    intro oc
    unfold searchAlg1Enum
    rw [if_pos h_ex]
    by_cases h1 : ∃ j, g j = true ∧ (∀ j', g j' = true → bitsToNat j ≤ bitsToNat j') ∧
        oc = (some j, c + bitsToNat j + 1)
    · rw [if_pos h1]
      rcases h1 with ⟨j, hj_true, hj_min, hoc⟩
      have h_eq : j = j₀ := h_inj (le_antisymm (hj_min j₀ hj₀_true) (hj₀_min j hj_true))
      subst h_eq
      rw [if_pos hoc]
    · rw [if_neg h1]
      have h2 : oc ≠ (some j₀, c + bitsToNat j₀ + 1) :=
        fun hoc => h1 ⟨j₀, hj₀_true, hj₀_min, hoc⟩
      rw [if_neg h2]
  refine ⟨?_, ?_⟩
  · simp_rw [h_enum_eq]
    exact tsum_ite_eq (some j₀, c + bitsToNat j₀ + 1) _
  · intro oc hoc
    rw [h_enum_eq] at hoc
    by_cases heq : oc = (some j₀, c + bitsToNat j₀ + 1)
    · subst heq
      dsimp
      omega
    · rw [if_neg heq] at hoc
      exact absurd rfl hoc

/-! ## Section 3: Potential Function `Ψ` and Expected Drop -/

private noncomputable def rankOf {n : ℕ} (f : Qubits n → ℤ) (l : Qubits n) : ℕ :=
  (Finset.univ.filter fun j => f j < f l).card

private noncomputable def psiPot (r : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 (r + 1), 1 / ((m : ℝ) * Real.sqrt (m : ℝ))

private lemma psiPot_zero : psiPot 0 = 0 := by
  simp [psiPot]

private lemma psiPot_nonneg (r : ℕ) : 0 ≤ psiPot r := by
  unfold psiPot
  refine Finset.sum_nonneg fun m _ => ?_
  positivity

private lemma psiPot_mono {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : psiPot r₁ ≤ psiPot r₂ := by
  unfold psiPot
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega)) ?_
  intro m _ _
  positivity

private lemma psiPot_sub_prev (r : ℕ) (hr : 1 ≤ r) :
    psiPot r - psiPot (r - 1) = 1 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
  unfold psiPot
  have hr_eq : r + 1 = (r - 1 + 1) + 1 := by omega
  have hr_sub : r - 1 + 1 = r := by omega
  rw [hr_eq, Finset.sum_Ico_succ_top (by omega), hr_sub]
  ring

private lemma psiPot_le_six (r : ℕ) : psiPot r ≤ 6 := by
  unfold psiPot
  have h_term : ∀ m ∈ Finset.Ico 1 (r + 1),
      1 / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤
        6 * (1 / Real.sqrt (m : ℝ) - 1 / Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hsm_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    have hsm1_pos : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hm1_pos
    have h_le2 : ((m + 1 : ℕ) : ℝ) ≤ 4 * (m : ℝ) := by
      push_cast
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    have h_sqrt_le : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
      have h_sqrt4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      calc Real.sqrt ((m + 1 : ℕ) : ℝ)
          ≤ Real.sqrt (4 * (m : ℝ)) := Real.sqrt_le_sqrt h_le2
        _ = 2 * Real.sqrt (m : ℝ) := by
            rw [Real.sqrt_mul (by norm_num), h_sqrt4]
    have h_diff : (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) *
        (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ)) = 1 := by
      calc (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) *
            (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ))
          = Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 - Real.sqrt (m : ℝ) ^ 2 := by ring
        _ = ((m + 1 : ℕ) : ℝ) - (m : ℝ) := by
            rw [Real.sq_sqrt hm1_pos.le, Real.sq_sqrt hm_pos.le]
        _ = 1 := by push_cast; ring
    have h_sum_le : Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ) ≤ 3 * Real.sqrt (m : ℝ) := by
      linarith
    have h_prod_le : (m : ℝ) * Real.sqrt (m : ℝ) * 6 *
        (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) ≥
        Real.sqrt (m : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
      have h_nonneg : 0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ) := by
        have : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
        exact sub_nonneg.mpr (Real.sqrt_le_sqrt this)
      calc Real.sqrt (m : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)
          ≤ Real.sqrt (m : ℝ) * (2 * Real.sqrt (m : ℝ)) :=
            mul_le_mul_of_nonneg_left h_sqrt_le hsm_pos.le
        _ = 2 * (m : ℝ) * 1 := by rw [mul_left_comm, ← sq, Real.sq_sqrt hm_pos.le]; ring
        _ = 2 * (m : ℝ) * ((Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) *
              (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ))) := by rw [h_diff]
        _ ≤ 2 * (m : ℝ) * ((Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) *
              (3 * Real.sqrt (m : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h_sum_le h_nonneg
        _ = (m : ℝ) * Real.sqrt (m : ℝ) * 6 *
              (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) := by ring
    have h_sub_div : 1 / Real.sqrt (m : ℝ) - 1 / Real.sqrt ((m + 1 : ℕ) : ℝ) =
        (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) /
          (Real.sqrt (m : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
      rw [div_sub_div _ _ hsm_pos.ne' hsm1_pos.ne']
      ring
    rw [h_sub_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h_sum_le := Finset.sum_le_sum h_term
  have h_tele_eq : ∀ k : ℕ,
      (∑ m ∈ Finset.Ico 1 (k + 1),
        6 * (1 / Real.sqrt (m : ℝ) - 1 / Real.sqrt ((m + 1 : ℕ) : ℝ))) =
        6 * (1 - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      ring
  have h_tele : (∑ m ∈ Finset.Ico 1 (r + 1),
      6 * (1 / Real.sqrt (m : ℝ) - 1 / Real.sqrt ((m + 1 : ℕ) : ℝ))) ≤ 6 := by
    rw [h_tele_eq r]
    have : 0 ≤ 1 / Real.sqrt ((r + 1 : ℕ) : ℝ) := by positivity
    linarith
  exact le_trans h_sum_le h_tele

private lemma sum_range_psiPot_sub (r : ℕ) (hr : 1 ≤ r) :
    Real.sqrt (r : ℝ) ≤ ∑ i ∈ Finset.range r, (psiPot r - psiPot i) := by
  have h_id : ∀ k : ℕ, (∑ i ∈ Finset.range k, (psiPot k - psiPot i)) =
      ∑ m ∈ Finset.Ico 1 (k + 1), 1 / Real.sqrt (m : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have h_split : (∑ i ∈ Finset.range (k + 1), (psiPot (k + 1) - psiPot i)) =
          (∑ i ∈ Finset.range (k + 1), (psiPot k - psiPot i)) +
            ∑ _i ∈ Finset.range (k + 1), (psiPot (k + 1) - psiPot k) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [h_split, Finset.sum_range_succ (fun i => psiPot k - psiPot i) k, sub_self, add_zero, ih,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      have h_step := psiPot_sub_prev (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h_step
      rw [h_step]
      have h_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [h_ne]
  rw [h_id r]
  have h_le : (∑ _m ∈ Finset.Ico 1 (r + 1), 1 / Real.sqrt (r : ℝ)) ≤
      ∑ m ∈ Finset.Ico 1 (r + 1), 1 / Real.sqrt (m : ℝ) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hmr : m ≤ r := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hm).2
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    refine one_div_le_one_div_of_le (Real.sqrt_pos.mpr hm_pos) (Real.sqrt_le_sqrt ?_)
    exact_mod_cast hmr
  rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul] at h_le
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h_cancel : (r : ℝ) * (1 / Real.sqrt (r : ℝ)) = Real.sqrt (r : ℝ) := by
    rw [mul_one_div, div_eq_iff (Real.sqrt_pos.mpr hr_pos).ne', ← sq, Real.sq_sqrt hr_pos.le]
  linarith

private lemma sum_rank_eq_sum_range {α : Type*} [DecidableEq α] (S : Finset α)
    (g : α → ℤ) (hg : Function.Injective g) (h : ℕ → ℝ) :
    (∑ j ∈ S, h ((S.filter fun j' => g j' < g j).card)) =
      ∑ i ∈ Finset.range S.card, h i := by
  induction hk : S.card generalizing S with
  | zero =>
    rw [Finset.card_eq_zero.mp hk]
    simp
  | succ k ih =>
    have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j₀, hj₀, hj₀_max⟩ := S.exists_max_image g hS_ne
    let S' := S.erase j₀
    have hS'_card : S'.card = k := by
      rw [Finset.card_erase_of_mem hj₀, hk]
      omega
    rw [← Finset.add_sum_erase S _ hj₀]
    have h_j₀ : S.filter (fun j' => g j' < g j₀) = S' := by
      ext j'
      simp only [S', Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hj'S, hlt⟩
        refine ⟨?_, hj'S⟩
        intro heq; subst heq; exact lt_irrefl _ hlt
      · rintro ⟨hne, hj'S⟩
        refine ⟨hj'S, lt_of_le_of_ne (hj₀_max j' hj'S) (fun heq => hne (hg heq))⟩
    have h_rest : ∀ j ∈ S',
        S.filter (fun j' => g j' < g j) = S'.filter (fun j' => g j' < g j) := by
      intro j hj
      ext j'
      simp only [S', Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hj'S, hlt⟩
        refine ⟨⟨?_, hj'S⟩, hlt⟩
        intro heq; subst heq
        exact not_lt_of_ge (hj₀_max j (Finset.mem_of_mem_erase hj)) hlt
      · rintro ⟨⟨_, hj'S⟩, hlt⟩
        exact ⟨hj'S, hlt⟩
    rw [h_j₀, hS'_card, Finset.sum_congr rfl (fun j hj => by rw [h_rest j hj]),
      ih S' hS'_card, Finset.sum_range_succ, add_comm]

private def fLex {n : ℕ} (f : Qubits n → ℤ) (j : Qubits n) : ℤ :=
  f j * (2 ^ n : ℤ) + (bitsToNat j : ℤ)

private lemma bitsToNat_lt_two_pow {n : ℕ} (j : Qubits n) : bitsToNat j < 2 ^ n := by
  rw [← bitsEquivFin_apply]
  exact (bitsEquivFin n j).isLt

private lemma fLex_injective {n : ℕ} (f : Qubits n → ℤ) : Function.Injective (fLex f) := by
  intro j₁ j₂ h
  unfold fLex at h
  have h1_raw : (bitsToNat j₁ : ℤ) < (2 : ℤ) ^ n := by exact_mod_cast bitsToNat_lt_two_pow j₁
  have h2_raw : (bitsToNat j₂ : ℤ) < (2 : ℤ) ^ n := by exact_mod_cast bitsToNat_lt_two_pow j₂
  set N : ℤ := (2 : ℤ) ^ n
  have h1 : (bitsToNat j₁ : ℤ) < N := h1_raw
  have h2 : (bitsToNat j₂ : ℤ) < N := h2_raw
  have h3 : (0 : ℤ) ≤ (bitsToNat j₁ : ℤ) := by positivity
  have h4 : (0 : ℤ) ≤ (bitsToNat j₂ : ℤ) := by positivity
  have h_fj : f j₁ = f j₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : f j₁ + 1 ≤ f j₂ := Int.add_one_le_iff.mpr hlt
      nlinarith
    · have : f j₂ + 1 ≤ f j₁ := Int.add_one_le_iff.mpr hgt
      nlinarith
  have h_eq_nat : bitsToNat j₁ = bitsToNat j₂ := by
    rw [h_fj] at h
    exact_mod_cast add_left_cancel h
  apply (bitsEquivFin n).injective
  apply Fin.ext
  rw [bitsEquivFin_apply, bitsEquivFin_apply, h_eq_nat]

private lemma fLex_lt_of_lt {n : ℕ} (f : Qubits n → ℤ) {j₁ j₂ : Qubits n}
    (h : f j₁ < f j₂) : fLex f j₁ < fLex f j₂ := by
  unfold fLex
  have h1 : (bitsToNat j₁ : ℤ) < (2 ^ n : ℤ) := by exact_mod_cast bitsToNat_lt_two_pow j₁
  have h2 : (0 : ℤ) ≤ (bitsToNat j₂ : ℤ) := by positivity
  have h3 : (0 : ℤ) < (2 ^ n : ℤ) := by positivity
  nlinarith

private lemma sum_marked_psiPot_sub_ge {n : ℕ} (f : Qubits n → ℤ) (l : Qubits n)
    (hr : 1 ≤ rankOf f l) :
    Real.sqrt (rankOf f l : ℝ) ≤
      ∑ j ∈ Finset.univ.filter (fun j => f j < f l),
        (psiPot (rankOf f l) - psiPot (rankOf f j)) := by
  set M := Finset.univ.filter (fun j => f j < f l)
  have hM_card : M.card = rankOf f l := rfl
  have h_le : ∀ j ∈ M,
      psiPot (rankOf f l) - psiPot ((M.filter fun j' => fLex f j' < fLex f j).card) ≤
        psiPot (rankOf f l) - psiPot (rankOf f j) := by
    intro j hj
    have hj_lt : f j < f l := (Finset.mem_filter.mp hj).2
    have h_sub : Finset.univ.filter (fun j' => f j' < f j) ⊆
        M.filter (fun j' => fLex f j' < fLex f j) := by
      intro j' hj'
      have hj'_lt : f j' < f j := (Finset.mem_filter.mp hj').2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j', lt_trans hj'_lt hj_lt⟩,
        fLex_lt_of_lt f hj'_lt⟩
    have h_card_le : rankOf f j ≤ (M.filter fun j' => fLex f j' < fLex f j).card :=
      Finset.card_le_card h_sub
    exact sub_le_sub_left (psiPot_mono h_card_le) _
  calc Real.sqrt (rankOf f l : ℝ)
      ≤ ∑ i ∈ Finset.range M.card, (psiPot (rankOf f l) - psiPot i) := by
          rw [hM_card]
          exact sum_range_psiPot_sub (rankOf f l) hr
    _ = ∑ j ∈ M, (psiPot (rankOf f l) - psiPot ((M.filter fun j' => fLex f j' < fLex f j).card)) := by
          rw [← sum_rank_eq_sum_range M (fLex f) (fLex_injective f)
            (fun i => psiPot (rankOf f l) - psiPot i)]
    _ ≤ ∑ j ∈ M, (psiPot (rankOf f l) - psiPot (rankOf f j)) :=
          Finset.sum_le_sum h_le

/-! ## Section 4: Expected Drop of `psiPot` under `searchAlg1Weight` and Supermartingale Bound -/

private abbrev nextIncumbent {n : ℕ} (f : Qubits n → ℤ) (l : Qubits n)
    (o : Option (Qubits n)) : Qubits n :=
  match o with
  | some k => if f k < f l then k else l
  | none => l

private lemma rankOf_lt_of_lt {n : ℕ} (f : Qubits n → ℤ) {k l : Qubits n}
    (hkl : f k < f l) : rankOf f k ≤ rankOf f l - 1 := by
  have h_sub : Finset.univ.filter (fun j => f j < f k) ⊆
      (Finset.univ.filter (fun j => f j < f l)).erase k := by
    intro j hj
    have hjk : f j < f k := (Finset.mem_filter.mp hj).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_trans hjk hkl⟩⟩
    intro heq; subst heq; exact lt_irrefl _ hjk
  have h_mem : k ∈ Finset.univ.filter (fun j => f j < f l) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkl⟩
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_erase_of_mem h_mem] at h_card
  exact h_card

private lemma rankOf_lt_two_pow {n : ℕ} (f : Qubits n → ℤ) (l : Qubits n) :
    rankOf f l < 2 ^ n := by
  have h_ssub : Finset.univ.filter (fun j => f j < f l) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, fun h_eq => ?_⟩
    have : l ∈ Finset.univ.filter (fun j => f j < f l) := h_eq.symm ▸ Finset.mem_univ l
    exact lt_irrefl (f l) (Finset.mem_filter.mp this).2
  have h_lt := Finset.card_lt_card h_ssub
  simpa [rankOf] using h_lt

private lemma tsum_option_fintype_prod_nat {α : Type*} [Fintype α] (w : Option α × ℕ → ℝ≥0∞) :
    (∑' oc : Option α × ℕ, w oc) =
      (∑' c : ℕ, w (none, c)) + ∑ a : α, ∑' c : ℕ, w (some a, c) := by
  rw [ENNReal.tsum_prod', tsum_fintype, Fintype.sum_option]

private lemma quant_expected_drop_ge {n : ℕ} (f : Qubits n → ℤ) (l : Qubits n)
    (hr : 1 ≤ rankOf f l) :
    let g : Qubits n → Bool := fun j => decide (f j < f l)
    (∑' oc : Option (Qubits n) × ℕ, searchAlg1Quant g (alg1RoundList n) 0 oc) *
      ENNReal.ofReal (1 / Real.sqrt (rankOf f l : ℝ)) ≤
      ∑' oc : Option (Qubits n) × ℕ, searchAlg1Quant g (alg1RoundList n) 0 oc *
        ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1))) := by
  intro g
  set M := Finset.univ.filter (fun j : Qubits n => f j < f l)
  have hM_nonempty : M.Nonempty := Finset.card_pos.mp (by omega : 0 < rankOf f l)
  obtain ⟨j₀, hj₀M⟩ := hM_nonempty
  have hj₀_true : g j₀ = true := by
    simpa [g] using (Finset.mem_filter.mp hj₀M).2
  set qItem : ℝ≥0∞ := ∑' c' : ℕ, searchAlg1Quant g (alg1RoundList n) 0 (some j₀, c')
  have h_none : ∀ c' : ℕ, searchAlg1Quant g (alg1RoundList n) 0 (none, c') = 0 := by
    intro c'
    exact searchAlg1Quant_eq_zero_of_not_marked g (alg1RoundList n) 0 (none, c') (by simp)
  have h_some_not : ∀ j : Qubits n, j ∉ M → ∀ c' : ℕ,
      searchAlg1Quant g (alg1RoundList n) 0 (some j, c') = 0 := by
    intro j hjM c'
    apply searchAlg1Quant_eq_zero_of_not_marked g (alg1RoundList n) 0 (some j, c')
    intro j' hj'
    injection hj' with hj'_eq
    subst hj'_eq
    simpa [g, M] using hjM
  have h_some_mem : ∀ j ∈ M,
      (∑' c' : ℕ, searchAlg1Quant g (alg1RoundList n) 0 (some j, c')) = qItem := by
    intro j hjM
    have hj_true : g j = true := by simpa [g] using (Finset.mem_filter.mp hjM).2
    refine tsum_congr fun c' => ?_
    exact searchAlg1Quant_some_eq_of_marked g (alg1RoundList n) 0 c' j j₀ hj_true hj₀_true
  have h_qTotal : (∑' oc : Option (Qubits n) × ℕ, searchAlg1Quant g (alg1RoundList n) 0 oc) =
      (rankOf f l : ℝ≥0∞) * qItem := by
    rw [tsum_option_fintype_prod_nat]
    simp_rw [h_none, tsum_zero, zero_add]
    rw [← Finset.sum_subset (Finset.subset_univ M)]
    · rw [Finset.sum_congr rfl h_some_mem, Finset.sum_const, nsmul_eq_mul]
      rfl
    · intro j _ hjM
      simp [h_some_not j hjM]
  have h_rhs : (∑' oc : Option (Qubits n) × ℕ, searchAlg1Quant g (alg1RoundList n) 0 oc *
      ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1)))) =
      qItem * ∑ j ∈ M, ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f j)) := by
    rw [tsum_option_fintype_prod_nat]
    have h_none_mul : (∑' c : ℕ, searchAlg1Quant g (alg1RoundList n) 0 (none, c) *
        ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l none)))) = 0 := by
      simp [h_none]
    rw [h_none_mul, zero_add, ← Finset.sum_subset (Finset.subset_univ M)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hjM => ?_
      have hj_lt : f j < f l := (Finset.mem_filter.mp hjM).2
      have h_inc : nextIncumbent f l (some j) = j := by simp [nextIncumbent, hj_lt]
      simp_rw [h_inc, ENNReal.tsum_mul_right, h_some_mem j hjM]
    · intro j _ hjM
      simp [h_some_not j hjM]
  rw [h_qTotal, h_rhs, mul_comm (rankOf f l : ℝ≥0∞) qItem, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le : (0 : ℝ≥0∞) ≤ qItem)
  have h_nonneg : ∀ j ∈ M, 0 ≤ psiPot (rankOf f l) - psiPot (rankOf f j) := by
    intro j hjM
    have hj_lt : f j < f l := (Finset.mem_filter.mp hjM).2
    have h_rank_le : rankOf f j ≤ rankOf f l := by
      have := rankOf_lt_of_lt f hj_lt
      omega
    exact sub_nonneg.mpr (psiPot_mono h_rank_le)
  rw [← ENNReal.ofReal_sum_of_nonneg h_nonneg]
  have hr_pos : (0 : ℝ) < (rankOf f l : ℝ) := by exact_mod_cast hr
  have h_r_cast : (rankOf f l : ℝ≥0∞) = ENNReal.ofReal (rankOf f l : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  rw [h_r_cast, ← ENNReal.ofReal_mul hr_pos.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_prod : (rankOf f l : ℝ) * (1 / Real.sqrt (rankOf f l : ℝ)) =
      Real.sqrt (rankOf f l : ℝ) := by
    rw [mul_one_div, div_eq_iff (Real.sqrt_pos.mpr hr_pos).ne', ← sq, Real.sq_sqrt hr_pos.le]
  rw [h_prod]
  exact sum_marked_psiPot_sub_ge f l hr

private lemma ofReal_one_half : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

private lemma ofReal_one_third : ENNReal.ofReal (1 / 3 : ℝ) = (1 / 3 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

private lemma le_of_mul_le_mul_left_ennreal {a b c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : c * a ≤ c * b) : a ≤ b := by
  calc a = c⁻¹ * (c * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    _ ≤ c⁻¹ * (c * b) := mul_le_mul_of_nonneg_left h zero_le
    _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

private lemma tsum_finset_sum {α β : Type*} (s : Finset α) (f : α → β → ℝ≥0∞) :
    (∑' b : β, ∑ a ∈ s, f a b) = ∑ a ∈ s, ∑' b : β, f a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [ENNReal.tsum_add, ih]

private lemma searchAlg1Weight_tsum_eq_one {n : ℕ} (g : Qubits n → Bool) :
    (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight g oc) = 1 := by
  by_cases h_card : 1 ≤ (Finset.univ.filter fun j => g j = true).card
  · obtain ⟨C₀, _, hC₀⟩ := quantumSearch_unknownCount_sqrt
    exact (hC₀ n g h_card).1
  · obtain ⟨C₁, _, hC₁⟩ := quantumSearch_unknownCount
    have h0 : (Finset.univ.filter fun j => g j = true).card = 0 := by omega
    have h_angle : groverAngle (Finset.univ.filter fun j => g j = true).card (2 ^ n) = 0 := by
      simp [groverAngle, h0]
    exact ((hC₁ n g).2 h_angle).1

private lemma searchAlg1Weight_expected_drop_ge {n : ℕ} (C₀ : ℝ) (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ (n' : ℕ) (g : Qubits n' → Bool),
      1 ≤ (Finset.univ.filter fun j => g j = true).card →
        (∑' oc : Option (Qubits n') × ℕ, searchAlg1Weight g oc) = 1 ∧
        (∀ oc : Option (Qubits n') × ℕ, searchAlg1Weight g oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ g j = true) ∧
        searchAlg1ExpectedCost g ≤
          ENNReal.ofReal (C₀ * Real.sqrt ((2 : ℝ) ^ n' /
            ((Finset.univ.filter fun j => g j = true).card : ℝ))))
    (f : Qubits n → ℤ) (l : Qubits n) (hr : 1 ≤ rankOf f l) :
    let M_thresh : ℝ := max 4 ((2 * C₀) ^ 2)
    let α : ℝ := min (1 / 2) (1 / M_thresh)
    let g : Qubits n → Bool := fun j => decide (f j < f l)
    ENNReal.ofReal (α * (1 / Real.sqrt (rankOf f l : ℝ))) ≤
      ∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight g oc *
        ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1))) := by
  intro M_thresh α g
  have h_card : (Finset.univ.filter fun j => g j = true).card = rankOf f l := by
    simp [g, rankOf]
  have h_card_ge : 1 ≤ (Finset.univ.filter fun j => g j = true).card := h_card ▸ hr
  obtain ⟨h_tsum, h_supp, h_cost⟩ := hC₀ n g h_card_ge
  have hM_pos : 0 < M_thresh := by positivity
  have hα_pos : 0 < α := lt_min (by norm_num) (one_div_pos.mpr hM_pos)
  by_cases h_large : 2 ≤ n ∧ (2 * C₀) ^ 2 ≤ (2 : ℝ) ^ n
  · obtain ⟨hn2, h_pow_ge⟩ := h_large
    have h_ex : ∃ j, g j = true := by
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter fun j => g j = true).card)
      exact ⟨j, (Finset.mem_filter.mp hj).2⟩
    obtain ⟨h_enum_tsum, h_enum_cost⟩ :=
      searchAlg1Enum_tsum_eq_one_of_marked g (roundsCost (alg1RoundList n)) h_ex
    set qTotal := ∑' oc : Option (Qubits n) × ℕ, searchAlg1Quant g (alg1RoundList n) 0 oc
    set pFail := searchAlg1FailProb g (alg1RoundList n)
    have h_sum_one : qTotal + pFail = 1 := by
      calc qTotal + pFail
          = qTotal + pFail * ∑' oc, searchAlg1Enum g (0 + roundsCost (alg1RoundList n)) oc := by
              rw [zero_add, h_enum_tsum, mul_one]
        _ = (∑' oc, searchAlg1Quant g (alg1RoundList n) 0 oc) +
              ∑' oc, pFail * searchAlg1Enum g (0 + roundsCost (alg1RoundList n)) oc := by
              rw [ENNReal.tsum_mul_left]
        _ = ∑' oc, (searchAlg1Quant g (alg1RoundList n) 0 oc +
              pFail * searchAlg1Enum g (0 + roundsCost (alg1RoundList n)) oc) := by
              rw [← ENNReal.tsum_add]
        _ = ∑' oc, searchAlg1Weight g oc := by
              refine tsum_congr fun oc => ?_
              exact (searchAlg1Rounds_eq_quant_add_enum g (alg1RoundList n) 0 oc).symm
        _ = 1 := h_tsum
    have h_rcost : 2 ^ n ≤ roundsCost (alg1RoundList n) := two_pow_le_roundsCost_alg1RoundList n hn2
    have h_pFail_cost : pFail * ((2 ^ n : ℕ) : ℝ≥0∞) ≤ searchAlg1ExpectedCost g := by
      calc pFail * ((2 ^ n : ℕ) : ℝ≥0∞)
          = pFail * ∑' oc, searchAlg1Enum g (roundsCost (alg1RoundList n)) oc * ((2 ^ n : ℕ) : ℝ≥0∞) := by
              rw [ENNReal.tsum_mul_right, h_enum_tsum, one_mul]
        _ = ∑' oc, pFail * searchAlg1Enum g (roundsCost (alg1RoundList n)) oc * ((2 ^ n : ℕ) : ℝ≥0∞) := by
              rw [← ENNReal.tsum_mul_left]
              refine tsum_congr fun oc => by ring
        _ ≤ ∑' oc, searchAlg1Weight g oc * (oc.2 : ℝ≥0∞) := by
              refine ENNReal.tsum_le_tsum fun oc => ?_
              by_cases h_e0 : searchAlg1Enum g (roundsCost (alg1RoundList n)) oc = 0
              · simp [h_e0]
              · have hc_le : 2 ^ n ≤ oc.2 := le_trans h_rcost (h_enum_cost oc h_e0)
                have h_w_le : pFail * searchAlg1Enum g (roundsCost (alg1RoundList n)) oc ≤
                    searchAlg1Weight g oc := by
                  change pFail * searchAlg1Enum g (roundsCost (alg1RoundList n)) oc ≤
                    searchAlg1Rounds g (alg1RoundList n) 0 oc
                  rw [searchAlg1Rounds_eq_quant_add_enum g (alg1RoundList n) 0 oc, zero_add]
                  exact le_add_self
                exact mul_le_mul' h_w_le (Nat.cast_le.mpr hc_le)
        _ = searchAlg1ExpectedCost g := by
              unfold searchAlg1ExpectedCost
              refine tsum_congr fun oc => by ring
    have h_cost_bound : searchAlg1ExpectedCost g ≤ ((2 ^ n : ℕ) : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) := by
      calc searchAlg1ExpectedCost g
          ≤ ENNReal.ofReal (C₀ * Real.sqrt ((2 : ℝ) ^ n / (rankOf f l : ℝ))) := by
              simpa [h_card] using h_cost
        _ ≤ ENNReal.ofReal (C₀ * Real.sqrt ((2 : ℝ) ^ n)) := by
              refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC₀_pos.le)
              exact div_le_self (by positivity) (by exact_mod_cast hr)
        _ ≤ ENNReal.ofReal ((1 / (2 : ℝ)) * (2 : ℝ) ^ n) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have h_sqrt_ge : 2 * C₀ ≤ Real.sqrt ((2 : ℝ) ^ n) := by
                rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * C₀)]
                exact Real.sqrt_le_sqrt h_pow_ge
              have h_sq : Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ n :=
                Real.mul_self_sqrt (by positivity)
              nlinarith [Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
        _ = ((2 ^ n : ℕ) : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) := by
              rw [ENNReal.ofReal_mul (by norm_num), ofReal_one_half,
                show ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) by push_cast; rfl,
                ENNReal.ofReal_natCast, mul_comm]
    have h_pFail_le : pFail ≤ 1 / 2 := by
      have h_mul_le : ((2 ^ n : ℕ) : ℝ≥0∞) * pFail ≤ ((2 ^ n : ℕ) : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) := by
        rw [mul_comm]
        exact le_trans h_pFail_cost h_cost_bound
      exact le_of_mul_le_mul_left_ennreal (by positivity) (ENNReal.natCast_ne_top _) h_mul_le
    have h_qTotal_ge : (1 / 2 : ℝ≥0∞) ≤ qTotal := by
      have h1 : (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) ≤ qTotal + (1 / 2 : ℝ≥0∞) := by
        calc (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞)
            = 1 := by simpa [one_div] using ENNReal.inv_two_add_inv_two
          _ = qTotal + pFail := h_sum_one.symm
          _ ≤ qTotal + (1 / 2 : ℝ≥0∞) := add_le_add_right h_pFail_le qTotal
      exact ENNReal.le_of_add_le_add_right (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) h1
    have h_α_le : ENNReal.ofReal α ≤ qTotal := by
      calc ENNReal.ofReal α
          ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = 1 / 2 := ofReal_one_half
        _ ≤ qTotal := h_qTotal_ge
    calc ENNReal.ofReal (α * (1 / Real.sqrt (rankOf f l : ℝ)))
        = ENNReal.ofReal α * ENNReal.ofReal (1 / Real.sqrt (rankOf f l : ℝ)) :=
            ENNReal.ofReal_mul hα_pos.le
      _ ≤ qTotal * ENNReal.ofReal (1 / Real.sqrt (rankOf f l : ℝ)) :=
            mul_le_mul_of_nonneg_right h_α_le zero_le
      _ ≤ ∑' oc, searchAlg1Quant g (alg1RoundList n) 0 oc *
            ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1))) :=
            quant_expected_drop_ge f l hr
      _ ≤ ∑' oc, searchAlg1Weight g oc *
            ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1))) := by
            refine ENNReal.tsum_le_tsum fun oc => mul_le_mul_of_nonneg_right ?_ zero_le
            change searchAlg1Quant g (alg1RoundList n) 0 oc ≤
              searchAlg1Rounds g (alg1RoundList n) 0 oc
            rw [searchAlg1Rounds_eq_quant_add_enum g (alg1RoundList n) 0 oc]
            exact le_self_add
  · have h_pow_le : (2 : ℝ) ^ n ≤ M_thresh := by
      rcases not_and_or.mp h_large with hn_lt | h_pow_lt
      · have hn1 : n ≤ 1 := by omega
        have : (2 : ℝ) ^ n ≤ 4 := by
          rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> norm_num
        exact le_trans this (le_max_left 4 _)
      · exact le_trans (le_of_lt (not_le.mp h_pow_lt)) (le_max_right 4 _)
    have hr_le_M : (rankOf f l : ℝ) ≤ M_thresh := by
      have hr_lt : (rankOf f l : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast le_of_lt (rankOf_lt_two_pow f l)
      exact le_trans hr_lt h_pow_le
    calc ENNReal.ofReal (α * (1 / Real.sqrt (rankOf f l : ℝ)))
        = (∑' oc, searchAlg1Weight g oc) *
            ENNReal.ofReal (α * (1 / Real.sqrt (rankOf f l : ℝ))) := by
            rw [h_tsum, one_mul]
      _ = ∑' oc, searchAlg1Weight g oc *
            ENNReal.ofReal (α * (1 / Real.sqrt (rankOf f l : ℝ))) := by
            rw [ENNReal.tsum_mul_right]
      _ ≤ ∑' oc, searchAlg1Weight g oc *
            ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1))) := by
            refine ENNReal.tsum_le_tsum fun oc => ?_
            by_cases hw : searchAlg1Weight g oc = 0
            · simp [hw]
            · refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
              obtain ⟨k, hk_eq, hk_true⟩ := h_supp oc hw
              have hkl : f k < f l := by simpa [g] using hk_true
              have h_inc : nextIncumbent f l oc.1 = k := by simp [nextIncumbent, hk_eq, hkl]
              rw [h_inc]
              have h_rank_k : rankOf f k ≤ rankOf f l - 1 := rankOf_lt_of_lt f hkl
              have hr_pos : (0 : ℝ) < (rankOf f l : ℝ) := by exact_mod_cast hr
              calc α * (1 / Real.sqrt (rankOf f l : ℝ))
                  ≤ (1 / M_thresh) * (1 / Real.sqrt (rankOf f l : ℝ)) :=
                    mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
                _ ≤ (1 / (rankOf f l : ℝ)) * (1 / Real.sqrt (rankOf f l : ℝ)) :=
                    mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hr_pos hr_le_M) (by positivity)
                _ = 1 / ((rankOf f l : ℝ) * Real.sqrt (rankOf f l : ℝ)) := by ring
                _ = psiPot (rankOf f l) - psiPot (rankOf f l - 1) :=
                    (psiPot_sub_prev (rankOf f l) hr).symm
                _ ≤ psiPot (rankOf f l) - psiPot (rankOf f k) :=
                    sub_le_sub_left (psiPot_mono h_rank_k) _

private noncomputable def minFindFailProb {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (fuel : ℕ) (l : Qubits n) (q g : ℕ) : ℝ≥0∞ :=
  open Classical in
  ∑' out : Qubits n × ℕ × ℕ, if 1 ≤ rankOf f out.1 then minFindLoop f b T fuel l q g out else 0

private lemma minFindFailProb_zero {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (l : Qubits n) (q g : ℕ) :
    minFindFailProb f b T 0 l q g = if 1 ≤ rankOf f l then 1 else 0 := by
  classical
  unfold minFindFailProb minFindLoop
  have h : ∀ out : Qubits n × ℕ × ℕ,
      (if 1 ≤ rankOf f out.1 then if out = (l, q, g) then (1 : ℝ≥0∞) else 0 else 0) =
        if out = (l, q, g) then (if 1 ≤ rankOf f l then 1 else 0) else 0 := by
    intro out
    by_cases hout : out = (l, q, g)
    · subst hout; simp
    · simp [hout]
  simp_rw [h]
  exact tsum_ite_eq (l, q, g) _

private lemma minFindFailProb_succ {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (fuel : ℕ) (l : Qubits n) (q g : ℕ) :
    minFindFailProb f b T (fuel + 1) l q g =
      ∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight (fun j => decide (f j < f l)) oc *
        (if q + oc.2 ≤ T then
          minFindFailProb f b T fuel (nextIncumbent f l oc.1) (q + oc.2)
            (g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b)
        else if 1 ≤ rankOf f l then 1 else 0) := by
  classical
  unfold minFindFailProb
  simp only [minFindLoop]
  trans (∑' out : Qubits n × ℕ × ℕ,
    ∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight (fun j => decide (f j < f l)) oc *
      (if 1 ≤ rankOf f out.1 then
        (if q + oc.2 ≤ T then
          minFindLoop f b T fuel (nextIncumbent f l oc.1) (q + oc.2)
            (g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b) out
        else if out = (l, T, g + alg1Gates n b (alg1RoundList n) (T - q)) then 1 else 0)
      else 0))
  · refine tsum_congr fun out => ?_
    by_cases hr : 1 ≤ rankOf f out.1
    · rw [if_pos hr]
      refine tsum_congr fun oc => ?_
      rw [if_pos hr]
      rfl
    · simp [hr]
  · rw [ENNReal.tsum_comm]
    refine tsum_congr fun oc => ?_
    rw [ENNReal.tsum_mul_left]
    congr 1
    by_cases hqT : q + oc.2 ≤ T
    · simp only [if_pos hqT]
    · simp only [if_neg hqT]
      have h_pt : ∀ out : Qubits n × ℕ × ℕ,
          (if 1 ≤ rankOf f out.1 then
            if out = (l, T, g + alg1Gates n b (alg1RoundList n) (T - q)) then (1 : ℝ≥0∞) else 0
          else 0) =
          if out = (l, T, g + alg1Gates n b (alg1RoundList n) (T - q)) then
            (if 1 ≤ rankOf f l then 1 else 0)
          else 0 := by
        intro out
        by_cases hout : out = (l, T, g + alg1Gates n b (alg1RoundList n) (T - q))
        · subst hout; simp
        · simp [hout]
      simp_rw [h_pt]
      exact tsum_ite_eq (l, T, g + alg1Gates n b (alg1RoundList n) (T - q))
        (fun _ => if 1 ≤ rankOf f l then (1 : ℝ≥0∞) else 0)

private lemma minFindFailProb_eq_zero_of_rank_zero {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (fuel : ℕ) (l : Qubits n) (q g : ℕ) (hr : rankOf f l = 0) :
    minFindFailProb f b T fuel l q g = 0 := by
  induction fuel generalizing q g with
  | zero =>
    rw [minFindFailProb_zero, hr]
    simp
  | succ fuel ih =>
    rw [minFindFailProb_succ]
    have h_no_lt : ∀ k : Qubits n, ¬ (f k < f l) := by
      intro k hk
      have h_mem : k ∈ Finset.univ.filter (fun j => f j < f l) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      have h_pos : 0 < rankOf f l := Finset.card_pos.mpr ⟨k, h_mem⟩
      omega
    have h_inc : ∀ o : Option (Qubits n), nextIncumbent f l o = l := by
      intro o
      cases o with
      | none => rfl
      | some k => simp [nextIncumbent, h_no_lt k]
    simp_rw [h_inc, ih, hr]
    simp

private lemma minFindFailProb_bound {n : ℕ} (C₀ : ℝ) (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ (n' : ℕ) (g : Qubits n' → Bool),
      1 ≤ (Finset.univ.filter fun j => g j = true).card →
        (∑' oc : Option (Qubits n') × ℕ, searchAlg1Weight g oc) = 1 ∧
        (∀ oc : Option (Qubits n') × ℕ, searchAlg1Weight g oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ g j = true) ∧
        searchAlg1ExpectedCost g ≤
          ENNReal.ofReal (C₀ * Real.sqrt ((2 : ℝ) ^ n' /
            ((Finset.univ.filter fun j => g j = true).card : ℝ))))
    (f : Qubits n → ℤ) (b T : ℕ) (fuel : ℕ) (l : Qubits n) (q g : ℕ)
    (hfuel : T + 1 ≤ q + fuel) :
    let M_thresh : ℝ := max 4 ((2 * C₀) ^ 2)
    let α : ℝ := min (1 / 2) (1 / M_thresh)
    let B : ℝ := (C₀ / α) * Real.sqrt ((2 : ℝ) ^ n)
    ((T + 1 : ℕ) : ℝ≥0∞) * minFindFailProb f b T fuel l q g ≤
      (q : ℝ≥0∞) + ENNReal.ofReal (B * psiPot (rankOf f l)) := by
  intro M_thresh α B
  have hM_pos : 0 < M_thresh := by positivity
  have hα_pos : 0 < α := lt_min (by norm_num) (one_div_pos.mpr hM_pos)
  have hB_pos : 0 < B := by positivity
  induction fuel generalizing l q g with
  | zero =>
    rw [minFindFailProb_zero]
    have hTq : T + 1 ≤ q := by omega
    split_ifs with hr
    · rw [mul_one]
      exact le_trans (Nat.cast_le.mpr hTq) le_self_add
    · simp
  | succ fuel ih =>
    by_cases hr0 : rankOf f l = 0
    · rw [minFindFailProb_eq_zero_of_rank_zero f b T (fuel + 1) l q g hr0, mul_zero]
      exact zero_le
    · have hr : 1 ≤ rankOf f l := Nat.pos_of_ne_zero hr0
      rw [minFindFailProb_succ, ← ENNReal.tsum_mul_left]
      set g_mark : Qubits n → Bool := fun j => decide (f j < f l)
      have h_card : (Finset.univ.filter fun j => g_mark j = true).card = rankOf f l := by
        simp [g_mark, rankOf]
      obtain ⟨h_tsum, h_supp, h_cost⟩ := hC₀ n g_mark (h_card ▸ hr)
      have h_step_le : (∑' oc : Option (Qubits n) × ℕ,
          ((T + 1 : ℕ) : ℝ≥0∞) * (searchAlg1Weight g_mark oc *
            (if q + oc.2 ≤ T then
              minFindFailProb f b T fuel (nextIncumbent f l oc.1) (q + oc.2)
                (g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b)
            else if 1 ≤ rankOf f l then 1 else 0))) ≤
          ∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight g_mark oc *
            ((q : ℝ≥0∞) + (oc.2 : ℝ≥0∞) +
              ENNReal.ofReal (B * psiPot (rankOf f (nextIncumbent f l oc.1)))) := by
        refine ENNReal.tsum_le_tsum fun oc => ?_
        by_cases hw : searchAlg1Weight g_mark oc = 0
        · simp [hw]
        · rw [mul_left_comm]
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          have hoc_pos : 1 ≤ oc.2 := searchAlg1Weight_cost_pos g_mark oc hw
          split_ifs with hqT
          · have hfuel' : T + 1 ≤ (q + oc.2) + fuel := by omega
            have h_ih := ih (nextIncumbent f l oc.1) (q + oc.2)
              (g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b) hfuel'
            simpa [Nat.cast_add] using h_ih
          · rw [mul_one]
            have hTq : T + 1 ≤ q + oc.2 := by omega
            have h_cast : ((T + 1 : ℕ) : ℝ≥0∞) ≤ (q : ℝ≥0∞) + (oc.2 : ℝ≥0∞) := by
              exact_mod_cast hTq
            exact le_trans h_cast le_self_add
      refine le_trans h_step_le ?_
      have h_split : (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight g_mark oc *
          ((q : ℝ≥0∞) + (oc.2 : ℝ≥0∞) +
            ENNReal.ofReal (B * psiPot (rankOf f (nextIncumbent f l oc.1))))) =
          (q : ℝ≥0∞) + searchAlg1ExpectedCost g_mark +
            ∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight g_mark oc *
              ENNReal.ofReal (B * psiPot (rankOf f (nextIncumbent f l oc.1))) := by
        have h1 : ∀ oc : Option (Qubits n) × ℕ,
            searchAlg1Weight g_mark oc * ((q : ℝ≥0∞) + (oc.2 : ℝ≥0∞) +
              ENNReal.ofReal (B * psiPot (rankOf f (nextIncumbent f l oc.1)))) =
            searchAlg1Weight g_mark oc * (q : ℝ≥0∞) +
              searchAlg1Weight g_mark oc * (oc.2 : ℝ≥0∞) +
              searchAlg1Weight g_mark oc *
                ENNReal.ofReal (B * psiPot (rankOf f (nextIncumbent f l oc.1))) := by
          intro oc; ring
        simp_rw [h1, ENNReal.tsum_add, ENNReal.tsum_mul_right, h_tsum, one_mul]
        congr 2
        unfold searchAlg1ExpectedCost
        refine tsum_congr fun oc => by ring
      rw [h_split, add_assoc]
      refine add_le_add_right ?_ (q : ℝ≥0∞)
      have h_drop := searchAlg1Weight_expected_drop_ge C₀ hC₀_pos hC₀ f l hr
      have h_cost_B : searchAlg1ExpectedCost g_mark ≤
          ENNReal.ofReal B * ENNReal.ofReal (α * (1 / Real.sqrt (rankOf f l : ℝ))) := by
        have h_eq : C₀ * Real.sqrt ((2 : ℝ) ^ n / (rankOf f l : ℝ)) =
            B * (α * (1 / Real.sqrt (rankOf f l : ℝ))) := by
          rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
          dsimp [B]
          field_simp [hα_pos.ne']
        rw [← ENNReal.ofReal_mul hB_pos.le, ← h_eq]
        simpa [h_card] using h_cost
      have h_B_drop : ENNReal.ofReal B * ENNReal.ofReal (α * (1 / Real.sqrt (rankOf f l : ℝ))) ≤
          ∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight g_mark oc *
            ENNReal.ofReal (B * (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1)))) := by
        calc ENNReal.ofReal B * ENNReal.ofReal (α * (1 / Real.sqrt (rankOf f l : ℝ)))
            ≤ ENNReal.ofReal B * ∑' oc, searchAlg1Weight g_mark oc *
                ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1))) :=
              mul_le_mul_of_nonneg_left h_drop zero_le
          _ = ∑' oc, ENNReal.ofReal B * (searchAlg1Weight g_mark oc *
                ENNReal.ofReal (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1)))) := by
              rw [ENNReal.tsum_mul_left]
          _ = ∑' oc, searchAlg1Weight g_mark oc *
                ENNReal.ofReal (B * (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1)))) := by
              refine tsum_congr fun oc => ?_
              rw [mul_left_comm, ← ENNReal.ofReal_mul hB_pos.le]
      calc searchAlg1ExpectedCost g_mark +
            ∑' oc, searchAlg1Weight g_mark oc *
              ENNReal.ofReal (B * psiPot (rankOf f (nextIncumbent f l oc.1)))
          ≤ (∑' oc, searchAlg1Weight g_mark oc *
              ENNReal.ofReal (B * (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1))))) +
            ∑' oc, searchAlg1Weight g_mark oc *
              ENNReal.ofReal (B * psiPot (rankOf f (nextIncumbent f l oc.1))) :=
            add_le_add_left (le_trans h_cost_B h_B_drop) _
        _ = ∑' oc, (searchAlg1Weight g_mark oc *
              ENNReal.ofReal (B * (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1)))) +
            searchAlg1Weight g_mark oc *
              ENNReal.ofReal (B * psiPot (rankOf f (nextIncumbent f l oc.1)))) := by
            rw [← ENNReal.tsum_add]
        _ ≤ ∑' oc, searchAlg1Weight g_mark oc * ENNReal.ofReal (B * psiPot (rankOf f l)) := by
            refine ENNReal.tsum_le_tsum fun oc => ?_
            by_cases hw : searchAlg1Weight g_mark oc = 0
            · simp [hw]
            · rw [← mul_add]
              refine mul_le_mul_of_nonneg_left ?_ zero_le
              obtain ⟨k, hk_eq, hk_true⟩ := h_supp oc hw
              have hkl : f k < f l := by simpa [g_mark] using hk_true
              have h_inc : nextIncumbent f l oc.1 = k := by simp [nextIncumbent, hk_eq, hkl]
              have h_rank_le : rankOf f (nextIncumbent f l oc.1) ≤ rankOf f l := by
                rw [h_inc]
                have := rankOf_lt_of_lt f hkl
                omega
              have h_sub_nonneg : 0 ≤ B * (psiPot (rankOf f l) - psiPot (rankOf f (nextIncumbent f l oc.1))) :=
                mul_nonneg hB_pos.le (sub_nonneg.mpr (psiPot_mono h_rank_le))
              have h_pot_nonneg : 0 ≤ B * psiPot (rankOf f (nextIncumbent f l oc.1)) :=
                mul_nonneg hB_pos.le (psiPot_nonneg _)
              rw [← ENNReal.ofReal_add h_sub_nonneg h_pot_nonneg]
              refine ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
        _ = ENNReal.ofReal (B * psiPot (rankOf f l)) := by
            rw [ENNReal.tsum_mul_right, h_tsum, one_mul]

/-! ## Section 5: Total Mass of `minFindWeight` and Independent Repetitions -/

private lemma minFindLoop_tsum_eq_one {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (fuel : ℕ) (l : Qubits n) (q g : ℕ) :
    (∑' out : Qubits n × ℕ × ℕ, minFindLoop f b T fuel l q g out) = 1 := by
  induction fuel generalizing l q g with
  | zero =>
    unfold minFindLoop
    exact tsum_ite_eq (l, q, g) _
  | succ fuel ih =>
    simp only [minFindLoop]
    rw [ENNReal.tsum_comm]
    trans (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight (fun j => decide (f j < f l)) oc)
    · refine tsum_congr fun oc => ?_
      rw [ENNReal.tsum_mul_left]
      split_ifs with hqT
      · rw [ih, mul_one]
      · rw [tsum_ite_eq, mul_one]
    · exact searchAlg1Weight_tsum_eq_one _

private lemma minFindWeight_tsum_eq_one {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ) :
    (∑' out : Qubits n × ℕ × ℕ, minFindWeight f b T out) = 1 := by
  unfold minFindWeight
  rw [tsum_finset_sum]
  simp_rw [ENNReal.tsum_mul_left, minFindLoop_tsum_eq_one, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.mul_inv_cancel (by positivity) (ENNReal.pow_ne_top (by norm_num))

private lemma tsum_pi_prod {α : Type*} (k : ℕ) (v : α → ℝ≥0∞) :
    (∑' outs : Fin k → α, ∏ i : Fin k, v (outs i)) = (∑' x : α, v x) ^ k := by
  induction k with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, pow_zero]
    rw [tsum_fintype]
    simp
  | succ k ih =>
    let e : α × (Fin k → α) ≃ (Fin (k + 1) → α) :=
      Fin.consEquiv (fun _ : Fin (k + 1) => α)
    rw [← e.tsum_eq]
    have h_prod : ∀ p : α × (Fin k → α),
        (∏ i : Fin (k + 1), v (e p i)) = v p.1 * ∏ i : Fin k, v (p.2 i) := by
      intro p
      exact Fin.prod_univ_succ (fun i => v (e p i))
    simp_rw [h_prod]
    rw [ENNReal.tsum_prod', pow_succ']
    simp_rw [ENNReal.tsum_mul_left, ih, ← ENNReal.tsum_mul_right]

private lemma prod_ite_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → Prop) [DecidablePred P] (f : ι → ℝ≥0∞) :
    (∏ i ∈ s, if P i then f i else 0) = if ∀ i ∈ s, P i then ∏ i ∈ s, f i else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih]
    by_cases hPa : P a
    · by_cases hPs : ∀ i ∈ s, P i
      · have h_all : ∀ i ∈ insert a s, P i := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact hPa
          · exact hPs i his
        rw [if_pos hPa, if_pos hPs, if_pos h_all, Finset.prod_insert ha]
      · have h_not : ¬ (∀ i ∈ insert a s, P i) :=
          fun h => hPs (fun i hi => h i (Finset.mem_insert_of_mem hi))
        rw [if_pos hPa, if_neg hPs, if_neg h_not, mul_zero]
    · have h_not : ¬ (∀ i ∈ insert a s, P i) :=
        fun h => hPa (h a (Finset.mem_insert_self a s))
      rw [if_neg hPa, if_neg h_not, zero_mul]

private lemma minFindRepeatProb_add_fail_pow {n : ℕ} (f : Qubits n → ℤ) (b T k : ℕ) :
    minFindRepeatProb f b T k (fun outs => ∃ i, ∀ j, f (outs i).1 ≤ f j) +
      (∑' out : Qubits n × ℕ × ℕ,
        if 1 ≤ rankOf f out.1 then minFindWeight f b T out else 0) ^ k = 1 := by
  classical
  unfold minFindRepeatProb
  have h_rank_iff : ∀ x : Qubits n, (1 ≤ rankOf f x) ↔ ¬ (∀ j, f x ≤ f j) := by
    intro x
    unfold rankOf
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos,
      Finset.filter_nonempty_iff]
    simp only [Finset.mem_univ, true_and, not_forall, not_le]
  have h_fail_pow : (∑' out : Qubits n × ℕ × ℕ,
      if 1 ≤ rankOf f out.1 then minFindWeight f b T out else 0) ^ k =
      ∑' outs : Fin k → Qubits n × ℕ × ℕ,
        if ¬ (∃ i, ∀ j, f (outs i).1 ≤ f j) then ∏ i, minFindWeight f b T (outs i) else 0 := by
    rw [← tsum_pi_prod k (fun out => if 1 ≤ rankOf f out.1 then minFindWeight f b T out else 0)]
    refine tsum_congr fun outs => ?_
    rw [prod_ite_zero Finset.univ (fun i : Fin k => 1 ≤ rankOf f (outs i).1)
      (fun i => minFindWeight f b T (outs i))]
    have h_iff : (∀ i ∈ (Finset.univ : Finset (Fin k)), 1 ≤ rankOf f (outs i).1) ↔
        ¬ (∃ i : Fin k, ∀ j, f (outs i).1 ≤ f j) := by
      simp_rw [Finset.mem_univ, true_implies, h_rank_iff, not_exists]
    by_cases h_cond : ∃ i : Fin k, ∀ j, f (outs i).1 ≤ f j
    · have h_not : ¬ (∀ i ∈ (Finset.univ : Finset (Fin k)), 1 ≤ rankOf f (outs i).1) := by
        rw [h_iff]; exact not_not.mpr h_cond
      rw [if_neg h_not, if_neg (not_not.mpr h_cond)]
    · have h_yes : ∀ i ∈ (Finset.univ : Finset (Fin k)), 1 ≤ rankOf f (outs i).1 :=
        h_iff.mpr h_cond
      rw [if_pos h_yes, if_pos h_cond]
  rw [h_fail_pow, ← ENNReal.tsum_add]
  trans (∑' outs : Fin k → Qubits n × ℕ × ℕ, ∏ i, minFindWeight f b T (outs i))
  · refine tsum_congr fun outs => ?_
    dsimp only
    by_cases h_ex : ∃ i, ∀ j, f (outs i).1 ≤ f j <;> simp [h_ex]
  · rw [tsum_pi_prod, minFindWeight_tsum_eq_one, one_pow]

private lemma inv_three_pow_ceil_logb_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (1 / 3 : ℝ) ^ ⌈Real.logb 3 (1 / δ)⌉₊ ≤ δ := by
  have h_inv_gt : 1 < 1 / δ := one_lt_one_div hδ0 hδ1
  have h_logb_nonneg : 0 ≤ Real.logb 3 (1 / δ) :=
    Real.logb_nonneg (by norm_num) h_inv_gt.le
  have h_ceil_ge : Real.logb 3 (1 / δ) ≤ (⌈Real.logb 3 (1 / δ)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h_rpow : (3 : ℝ) ^ Real.logb 3 (1 / δ) ≤ (3 : ℝ) ^ (⌈Real.logb 3 (1 / δ)⌉₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h_ceil_ge
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast] at h_rpow
  have h_pow_pos : (0 : ℝ) < (3 : ℝ) ^ ⌈Real.logb 3 (1 / δ)⌉₊ := by positivity
  rw [one_div_pow, one_div_le h_pow_pos hδ0]
  exact h_rpow

private lemma ceil_logb_three_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (⌈Real.logb 3 (1 / δ)⌉₊ : ℝ) ≤ 2 * (1 + Real.log (1 / δ)) := by
  have h_inv_gt : 1 < 1 / δ := one_lt_one_div hδ0 hδ1
  have h_log_pos : 0 < Real.log (1 / δ) := Real.log_pos h_inv_gt
  have h_logb_pos : 0 < Real.logb 3 (1 / δ) := Real.logb_pos (by norm_num) h_inv_gt
  have h_ceil_lt : (⌈Real.logb 3 (1 / δ)⌉₊ : ℝ) ≤ Real.logb 3 (1 / δ) + 1 :=
    (Nat.ceil_lt_add_one h_logb_pos.le).le
  have h_log3_ge_one : 1 ≤ Real.log 3 := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    linarith
  have h_logb_le : Real.logb 3 (1 / δ) ≤ Real.log (1 / δ) := by
    rw [Real.logb]
    exact div_le_self h_log_pos.le h_log3_ge_one
  linarith

end SolQuantumMinimumFinding

open SolQuantumMinimumFinding

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n b : ℕ) (f : Qubits n → ℤ), (∀ j, |f j| < 2 ^ b) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        ENNReal.ofReal (1 - δ) ≤
            minFindRepeatProb f b ⌈c * Real.sqrt ((2 : ℝ) ^ n)⌉₊ ⌈Real.logb 3 (1 / δ)⌉₊
              (fun outs => ∃ i, ∀ j, f (outs i).1 ≤ f j) ∧
        ∀ outs : Fin ⌈Real.logb 3 (1 / δ)⌉₊ → Qubits n × ℕ × ℕ,
          (∏ i, minFindWeight f b ⌈c * Real.sqrt ((2 : ℝ) ^ n)⌉₊ (outs i)) ≠ 0 →
            (((∑ i, (outs i).2.1) + ⌈Real.logb 3 (1 / δ)⌉₊ : ℕ) : ℝ) ≤
                C * Real.sqrt ((2 : ℝ) ^ n) * (1 + Real.log (1 / δ)) ∧
            (((∑ i, (outs i).2.2) + ⌈Real.logb 3 (1 / δ)⌉₊ * mfStepGates n b : ℕ) : ℝ) ≤
                C * Real.sqrt ((2 : ℝ) ^ n) * ((n + b + 1 : ℕ) : ℝ) * (1 + Real.log (1 / δ)) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := quantumSearch_unknownCount_sqrt
  let M_thresh : ℝ := max 4 ((2 * C₀) ^ 2)
  have hM_pos : 0 < M_thresh := by positivity
  let α : ℝ := min (1 / 2) (1 / M_thresh)
  have hα_pos : 0 < α := lt_min (by norm_num) (one_div_pos.mpr hM_pos)
  let c : ℝ := 18 * (C₀ / α)
  have hc_pos : 0 < c := by positivity
  let C : ℝ := 78 * (c + 2)
  have hC_pos : 0 < C := by positivity
  refine ⟨c, hc_pos, C, hC_pos, ?_⟩
  intro n b f _hf δ hδ0 hδ1
  set T : ℕ := ⌈c * Real.sqrt ((2 : ℝ) ^ n)⌉₊
  set k : ℕ := ⌈Real.logb 3 (1 / δ)⌉₊
  let B : ℝ := (C₀ / α) * Real.sqrt ((2 : ℝ) ^ n)
  refine ⟨?_, ?_⟩
  · -- Part 1: Success probability
    have h_18B : 18 * B ≤ ((T + 1 : ℕ) : ℝ) := by
      have h_ceil : c * Real.sqrt ((2 : ℝ) ^ n) ≤ (T : ℝ) := Nat.le_ceil _
      have h_eq : 18 * B = c * Real.sqrt ((2 : ℝ) ^ n) := by dsimp [c, B]; ring
      push_cast
      linarith
    have h_l_fail : ∀ l : Qubits n,
        minFindFailProb f b T (T + 1) l 0 0 ≤ (1 / 3 : ℝ≥0∞) := by
      intro l
      have h_bm := minFindFailProb_bound C₀ hC₀_pos hC₀ f b T (T + 1) l 0 0 (by omega)
      simp only [Nat.cast_zero, zero_add] at h_bm
      have h_psi6 : B * psiPot (rankOf f l) ≤ (1 / 3 : ℝ) * ((T + 1 : ℕ) : ℝ) := by
        have h6 := psiPot_le_six (rankOf f l)
        have hB_nonneg : 0 ≤ B := by positivity
        nlinarith
      have h_rhs : ENNReal.ofReal (B * psiPot (rankOf f l)) ≤
          ((T + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) := by
        calc ENNReal.ofReal (B * psiPot (rankOf f l))
            ≤ ENNReal.ofReal ((1 / 3 : ℝ) * ((T + 1 : ℕ) : ℝ)) := ENNReal.ofReal_le_ofReal h_psi6
          _ = ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal ((T + 1 : ℕ) : ℝ) :=
              ENNReal.ofReal_mul (by norm_num)
          _ = ((T + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) := by
              rw [ofReal_one_third, ENNReal.ofReal_natCast, mul_comm]
      have h_mul := le_trans h_bm h_rhs
      exact le_of_mul_le_mul_left_ennreal (by positivity) (ENNReal.natCast_ne_top _) h_mul
    have h_pfail_le : (∑' out : Qubits n × ℕ × ℕ,
        if 1 ≤ rankOf f out.1 then minFindWeight f b T out else 0) ≤ (1 / 3 : ℝ≥0∞) := by
      classical
      have h_eq : (∑' out : Qubits n × ℕ × ℕ,
          if 1 ≤ rankOf f out.1 then minFindWeight f b T out else 0) =
          ∑ l : Qubits n, ((2 : ℝ≥0∞) ^ n)⁻¹ * minFindFailProb f b T (T + 1) l 0 0 := by
        unfold minFindWeight minFindFailProb
        have h_ite : ∀ out : Qubits n × ℕ × ℕ,
            (if 1 ≤ rankOf f out.1 then
              ∑ l : Qubits n, ((2 : ℝ≥0∞) ^ n)⁻¹ * minFindLoop f b T (T + 1) l 0 0 out
            else 0) =
            ∑ l : Qubits n, ((2 : ℝ≥0∞) ^ n)⁻¹ *
              (if 1 ≤ rankOf f out.1 then minFindLoop f b T (T + 1) l 0 0 out else 0) := by
          intro out
          by_cases hr : 1 ≤ rankOf f out.1 <;> simp [hr]
        simp_rw [h_ite]
        rw [tsum_finset_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [ENNReal.tsum_mul_left]
      rw [h_eq]
      calc (∑ l : Qubits n, ((2 : ℝ≥0∞) ^ n)⁻¹ * minFindFailProb f b T (T + 1) l 0 0)
          ≤ ∑ _l : Qubits n, ((2 : ℝ≥0∞) ^ n)⁻¹ * (1 / 3 : ℝ≥0∞) :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h_l_fail l) zero_le
        _ = (1 / 3 : ℝ≥0∞) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
              Finset.prod_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
              ← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (ENNReal.pow_ne_top (by norm_num)),
              one_mul]
    have h_pow_le : (∑' out : Qubits n × ℕ × ℕ,
        if 1 ≤ rankOf f out.1 then minFindWeight f b T out else 0) ^ k ≤ ENNReal.ofReal δ := by
      calc (∑' out : Qubits n × ℕ × ℕ,
            if 1 ≤ rankOf f out.1 then minFindWeight f b T out else 0) ^ k
          ≤ (1 / 3 : ℝ≥0∞) ^ k := pow_le_pow_left' h_pfail_le k
        _ = ENNReal.ofReal ((1 / 3 : ℝ) ^ k) := by
            rw [ENNReal.ofReal_pow (by norm_num), ofReal_one_third]
        _ ≤ ENNReal.ofReal δ :=
            ENNReal.ofReal_le_ofReal (inv_three_pow_ceil_logb_le hδ0 hδ1)
    have h_add_one := minFindRepeatProb_add_fail_pow f b T k
    have h_sum_delta : ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) hδ0.le]
      ring_nf
      exact ENNReal.ofReal_one
    have h_le_add : ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ ≤
        minFindRepeatProb f b T k (fun outs => ∃ i, ∀ j, f (outs i).1 ≤ f j) +
          ENNReal.ofReal δ := by
      rw [h_sum_delta, ← h_add_one]
      exact add_le_add_right h_pow_le _
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h_le_add
  · -- Part 2: Query and gate bounds on support
    intro outs h_prod_ne
    have h_each : ∀ i : Fin k, (outs i).2.1 ≤ T ∧ (outs i).2.2 ≤ 12 * T * mfStepGates n b := by
      intro i
      have hi : minFindWeight f b T (outs i) ≠ 0 := by
        intro h0
        exact h_prod_ne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
      exact minFindWeight_support_bounds f b T (outs i) hi
    have h_q_sum : (∑ i : Fin k, (outs i).2.1) + k ≤ k * (T + 1) := by
      calc (∑ i : Fin k, (outs i).2.1) + k
          ≤ (∑ _i : Fin k, T) + k :=
            Nat.add_le_add_right (Finset.sum_le_sum fun i _ => (h_each i).1) k
        _ = k * (T + 1) := by simp [Finset.sum_const]; ring
    have h_g_sum : (∑ i : Fin k, (outs i).2.2) + k * mfStepGates n b ≤
        k * (12 * T + 1) * mfStepGates n b := by
      calc (∑ i : Fin k, (outs i).2.2) + k * mfStepGates n b
          ≤ (∑ _i : Fin k, 12 * T * mfStepGates n b) + k * mfStepGates n b :=
            Nat.add_le_add_right (Finset.sum_le_sum fun i _ => (h_each i).2) _
        _ = k * (12 * T + 1) * mfStepGates n b := by simp [Finset.sum_const]; ring
    have h_sqrt_ge_one : 1 ≤ Real.sqrt ((2 : ℝ) ^ n) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num))
    have h_T_plus_one : ((T + 1 : ℕ) : ℝ) ≤ (c + 2) * Real.sqrt ((2 : ℝ) ^ n) := by
      have h_lt : (T : ℝ) ≤ c * Real.sqrt ((2 : ℝ) ^ n) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      push_cast
      nlinarith
    have h_12T_plus_one : ((12 * T + 1 : ℕ) : ℝ) ≤ 13 * (c + 2) * Real.sqrt ((2 : ℝ) ^ n) := by
      have h_lt : (T : ℝ) ≤ c * Real.sqrt ((2 : ℝ) ^ n) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      push_cast
      nlinarith
    have h_k_le : (k : ℝ) ≤ 2 * (1 + Real.log (1 / δ)) := ceil_logb_three_le hδ0 hδ1
    have h_step_le : (mfStepGates n b : ℝ) ≤ 3 * ((n + b + 1 : ℕ) : ℝ) := by
      unfold mfStepGates
      push_cast
      linarith
    have h_log_pos : 0 < 1 + Real.log (1 / δ) := by
      have : 0 < Real.log (1 / δ) := Real.log_pos (one_lt_one_div hδ0 hδ1)
      linarith
    refine ⟨?_, ?_⟩
    · calc (((∑ i : Fin k, (outs i).2.1) + k : ℕ) : ℝ)
          ≤ ((k * (T + 1) : ℕ) : ℝ) := by exact_mod_cast h_q_sum
        _ = (k : ℝ) * ((T + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (2 * (1 + Real.log (1 / δ))) * ((c + 2) * Real.sqrt ((2 : ℝ) ^ n)) :=
            mul_le_mul h_k_le h_T_plus_one (by positivity) (by positivity)
        _ ≤ C * Real.sqrt ((2 : ℝ) ^ n) * (1 + Real.log (1 / δ)) := by
            dsimp [C]
            nlinarith
    · calc (((∑ i : Fin k, (outs i).2.2) + k * mfStepGates n b : ℕ) : ℝ)
          ≤ ((k * (12 * T + 1) * mfStepGates n b : ℕ) : ℝ) := by exact_mod_cast h_g_sum
        _ = (k : ℝ) * ((12 * T + 1 : ℕ) : ℝ) * (mfStepGates n b : ℝ) := by push_cast; ring
        _ ≤ (2 * (1 + Real.log (1 / δ))) * (13 * (c + 2) * Real.sqrt ((2 : ℝ) ^ n)) *
              (3 * ((n + b + 1 : ℕ) : ℝ)) := by
            refine mul_le_mul (mul_le_mul h_k_le h_12T_plus_one (by positivity) (by positivity))
              h_step_le (by positivity) (by positivity)
        _ = C * Real.sqrt ((2 : ℝ) ^ n) * ((n + b + 1 : ℕ) : ℝ) * (1 + Real.log (1 / δ)) := by
            dsimp [C]
            ring
