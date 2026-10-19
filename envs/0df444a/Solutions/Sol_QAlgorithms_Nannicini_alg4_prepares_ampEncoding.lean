-- Prove2me | solution 1 for QAlgorithms.Nannicini.alg4_prepares_ampEncoding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:55:19.985345+00:00
-- url     : https://prove2.me/submissions/ac12e500-fef5-4331-8cb9-1d06dd4eacc6

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05c_Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option autoImplicit false
set_option maxHeartbeats 1600000
open QAlgorithms
open scoped ComplexConjugate

private lemma prefix_agree {n k : ℕ} {y z : Qubits n}
    (h : ∀ a : Fin n, a.val < k → y a = z a) : prefixVal y k = prefixVal z k := by
  unfold prefixVal
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.val < k
  · rw [h a ha]
  · simp [ha]

private lemma prefix_succ {n : ℕ} (z : Qubits n) (k : Fin n) :
    prefixVal z (k.val + 1) = 2 * prefixVal z k.val + if z k then 1 else 0 := by
  classical
  unfold prefixVal
  rw [Finset.mul_sum]
  have ht : ∀ a : Fin n,
      (if a.val < k.val + 1 ∧ z a = true then 2 ^ (k.val + 1 - 1 - a.val) else 0) =
      2 * (if a.val < k.val ∧ z a = true then 2 ^ (k.val - 1 - a.val) else 0) +
      if a = k then (if z k then 1 else 0) else 0 := by
    intro a
    by_cases ha : a = k
    · subst a; simp
    · have hh : a.val ≠ k.val := fun h => ha (Fin.ext h)
      by_cases hl : a.val < k.val
      · have he : k.val - a.val = (k.val - 1 - a.val) + 1 := by omega
        simp [ha, hl, show a.val < k.val + 1 by omega, he, pow_succ, Nat.mul_comm]
      · simp [ha, hl, show ¬a.val < k.val + 1 by omega]
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  simp

private lemma prefix_final {n : ℕ} (z : Qubits n) : prefixVal z n = bitsToNat z := by
  unfold prefixVal bitsToNat
  apply Finset.sum_congr rfl
  intro a _
  simp [a.isLt]

private lemma tree_nonneg (n : ℕ) (x : Fin (2^n) → ℝ) (k j : ℕ) :
    0 ≤ ampTreeValue n x k j := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

private lemma tree_split (n : ℕ) (x : Fin (2^n) → ℝ) (k j : ℕ) (hk : k < n) :
    ampTreeValue n x k j = ampTreeValue n x (k+1) (2*j) +
      ampTreeValue n x (k+1) (2*j+1) := by
  classical
  unfold ampTreeValue
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : n-k = n-(k+1)+1 := by omega
  have hd : i.val / 2^(n-k) = (i.val / 2^(n-(k+1))) / 2 := by
    rw [he, pow_succ, Nat.div_div_eq_div_mul]
  by_cases h0 : i.val / 2^(n-(k+1)) = 2*j <;>
    by_cases h1 : i.val / 2^(n-(k+1)) = 2*j+1 <;>
    simp_all <;> omega

private lemma tree_root (n : ℕ) (x : Fin (2^n) → ℝ) :
    ampTreeValue n x 0 0 = ∑ i, x i ^ 2 := by
  unfold ampTreeValue
  congr 1
  ext i
  simp

private lemma tree_leaf (n : ℕ) (x : Fin (2^n) → ℝ) (z : Qubits n) :
    ampTreeValue n x n (prefixVal z n) = x (bitsEquivFin n z) ^ 2 := by
  classical
  simp only [ampTreeValue, Nat.sub_self, pow_zero, Nat.div_one, prefix_final,
    ← bitsEquivFin_apply]
  simp only [Fin.val_inj, Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]

private lemma rot_unitary (θ : ℝ) : rotY θ ∈ Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  have ht : (Real.cos (θ/2) : ℂ)^2 + (Real.sin (θ/2) : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (θ/2)
  ext a b
  cases a <;> cases b <;>
    simp only [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_bool, rotY,
      Matrix.of_apply, map_neg, Complex.star_def, Complex.conj_ofReal,
      Matrix.one_apply, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false] <;>
      first | linear_combination ht | ring

private lemma rot_weight (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (b : Bool) :
    (Real.sqrt (A+B) : ℂ) *
      rotY (2 * Real.arccos (Real.sqrt (A * (A+B)⁻¹))) b false =
      (Real.sqrt (if b then B else A) : ℂ) := by
  have hh : 0 ≤ A+B := add_nonneg hA hB
  by_cases hz : A+B = 0
  · have ha : A = 0 := by linarith
    have hb : B = 0 := by linarith
    subst A; subst B; cases b <;> simp [rotY]
  have hp : 0 < A+B := lt_of_le_of_ne hh (Ne.symm hz)
  have hv : 0 ≤ A * (A+B)⁻¹ := mul_nonneg hA (inv_nonneg.mpr hh)
  have hu : A * (A+B)⁻¹ ≤ 1 := by rw [← div_eq_mul_inv]; exact (div_le_one hp).mpr (by linarith)
  have hs : Real.sqrt (A * (A+B)⁻¹) ≤ 1 := by exact (Real.sqrt_le_one).mpr hu
  have hc := Real.cos_arccos (show -1 ≤ Real.sqrt (A * (A+B)⁻¹) by linarith [Real.sqrt_nonneg (A * (A+B)⁻¹)]) hs
  have h0 : Real.sqrt (A+B) * Real.sqrt (A * (A+B)⁻¹) = Real.sqrt A := by
    rw [← Real.sqrt_mul hh]
    congr 1
    field_simp
  have h1 : Real.sqrt (A+B) * Real.sin (Real.arccos (Real.sqrt (A * (A+B)⁻¹))) = Real.sqrt B := by
    rw [Real.sin_arccos, Real.sq_sqrt hv, ← Real.sqrt_mul hh]
    congr 1
    field_simp
    ring
  have hd : (2 * Real.arccos (Real.sqrt (A * (A+B)⁻¹))) / 2 =
      Real.arccos (Real.sqrt (A * (A+B)⁻¹)) := by ring
  cases b
  · simp only [rotY, Matrix.of_apply, hd, hc, Bool.false_eq_true, if_false]
    exact_mod_cast h0
  · simp only [rotY, Matrix.of_apply, hd, if_true]
    exact_mod_cast h1

private lemma step_unitary {n : ℕ} (x : Fin (2^n) → ℝ) (k : Fin n) :
    alg4Step n x k ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  classical
  let e := Equiv.funSplitAt k Bool
  let M : ({a : Fin n // a ≠ k} → Bool) → Matrix Bool Bool ℂ :=
    fun z => rotY (alg4Angle n x k (prefixVal (e.symm (false,z)) k))
  have heq : alg4Step n x k = (Matrix.blockDiagonal M).submatrix e e := by
    ext y z
    have he : (e y).2 = (e z).2 ↔ ∀ a, a ≠ k → y a = z a := by
      constructor
      · intro h a ha; exact congrFun h ⟨a,ha⟩
      · intro h; funext a; exact h a a.property
    have hp : prefixVal (e.symm (false,(e z).2)) k = prefixVal z k := by
      apply prefix_agree
      intro a ha
      have hak : a ≠ k := by intro h; subst a; omega
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hak]
    change (if ∀ a, a ≠ k → y a = z a then _ else _) =
      (if (e y).2 = (e z).2 then M ((e y).2) (y k) (z k) else 0)
    by_cases h : (e y).2 = (e z).2
    · simp only [if_pos (he.mp h), if_pos h]
      dsimp only [M]
      rw [h, hp]
    · simp only [if_neg (fun hh => h (he.mpr hh)), if_neg h]

  have hM : (Matrix.blockDiagonal M) * (Matrix.blockDiagonal M).conjTranspose = 1 := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    have h : (fun z => M z * (M z).conjTranspose) = 1 := by
      funext z
      exact (rot_unitary _).2
    rw [h, Matrix.blockDiagonal_one]
  apply Matrix.mem_unitaryGroup_iff.mpr
  change alg4Step n x k * (alg4Step n x k).conjTranspose = 1
  rw [heq, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hM,
    Matrix.submatrix_one_equiv]

private def tailZero {n : ℕ} (k : ℕ) (z : Qubits n) : Prop :=
  ∀ a : Fin n, k ≤ a.val → z a = false

private noncomputable def levelState (n : ℕ) (x : Fin (2^n) → ℝ) (k : ℕ) :
    EuclideanSpace ℂ (Qubits n) :=
  by
    classical
    exact WithLp.toLp 2 fun z => if tailZero k z then (Real.sqrt (ampTreeValue n x k (prefixVal z k)) : ℂ) else 0

private lemma step_level {n : ℕ} (x : Fin (2^n) → ℝ) (k : Fin n) :
    act (alg4Step n x k) (levelState n x k) = levelState n x (k.val+1) := by
  classical
  apply PiLp.ext
  intro y
  change (∑ z, alg4Step n x k y z * (levelState n x k) z) = _
  let z0 : Qubits n := Function.update y k false
  have hoff : ∀ a, a ≠ k → y a = z0 a := by
    intro a ha; simp [z0, Function.update_of_ne ha]
  have hp : prefixVal z0 k = prefixVal y k := by
    apply prefix_agree
    intro a ha
    have hak : a ≠ k := by intro h; subst a; omega
    simp [z0, Function.update_of_ne hak]
  by_cases hy : tailZero (k.val+1) y
  · have hz : tailZero k.val z0 := by
      intro a ha
      by_cases hak : a = k
      · subst a; simp [z0]
      · have hal : k.val+1 ≤ a.val := by have hh : a.val ≠ k.val := fun hh => hak (Fin.ext hh); omega
        simpa [z0, Function.update_of_ne hak] using hy a hal
    rw [Finset.sum_eq_single z0]
    · simp only [alg4Step, Matrix.of_apply, if_pos hoff, levelState, PiLp.toLp_apply,
        if_pos hz, if_pos hy, hp, show z0 k = false by simp [z0]]
      rw [prefix_succ y k, tree_split n x k (prefixVal y k) k.isLt]
      have h := rot_weight (ampTreeValue n x (k.val+1) (2*prefixVal y k))
        (ampTreeValue n x (k.val+1) (2*prefixVal y k+1))
        (tree_nonneg ..) (tree_nonneg ..) (y k)
      cases hb : y k <;> simpa [alg4Angle, hb, mul_comm] using h
    · intro z _ hzz
      by_cases h : ∀ a, a ≠ k → y a = z a
      · have ht : ¬ tailZero k.val z := by
          intro ht
          apply hzz
          funext a
          by_cases hak : a = k
          · subst a; simpa [z0] using ht k (le_refl _)
          · simpa [z0, Function.update_of_ne hak] using (h a hak).symm
        simp [levelState, ht]
      · simp [alg4Step, h]
    · simp
  · have hz : ∀ z, (∀ a, a ≠ k → y a = z a) → ¬ tailZero k.val z := by
      intro z hoff ht
      apply hy
      intro a ha
      have hak : a ≠ k := by intro h; subst a; omega
      rw [hoff a hak]
      exact ht a (by omega)
    rw [Finset.sum_eq_zero]
    · simp [levelState, hy]
    · intro z _
      by_cases h : ∀ a, a ≠ k → y a = z a
      · simp [levelState, hz z h]
      · simp [alg4Step, h]

private lemma level_zero (n : ℕ) (x : Fin (2^n) → ℝ) (hx : ∑ i, x i^2=1) :
    levelState n x 0 = zeroKet n := by
  classical
  apply PiLp.ext
  intro z
  have ht : tailZero 0 z ↔ z = fun _ => false := by
    simp [tailZero, funext_iff]
  simp [levelState, zeroKet, ket, ht, prefixVal, tree_root, hx, PiLp.single_apply]

private lemma product_level (n : ℕ) (x : Fin (2^n) → ℝ) (hx : ∑ i, x i^2=1)
    (k : ℕ) (hk : k ≤ n) :
    act (orderedProd (fun a : Fin k => alg4Step n x ⟨a, lt_of_lt_of_le a.isLt hk⟩))
      (zeroKet n) = levelState n x k := by
  induction k with
  | zero =>
      simp only [orderedProd, List.ofFn_zero, List.reverse_nil, List.prod_nil]
      simpa [act] using (level_zero n x hx).symm
  | succ k ih =>
      have hP : orderedProd (fun a : Fin (k+1) => alg4Step n x ⟨a, lt_of_lt_of_le a.isLt hk⟩) =
          alg4Step n x ⟨k, by omega⟩ *
            orderedProd (fun a : Fin k => alg4Step n x ⟨a, lt_of_lt_of_le a.isLt (show k ≤ n by omega)⟩) := by
        unfold orderedProd
        rw [List.ofFn_succ']
        simp only [List.concat_eq_append, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.prod_cons]
        rfl
      rw [hP]
      have hact (A B : Matrix (Qubits n) (Qubits n) ℂ) :
          act (A*B) (zeroKet n) = act A (act B (zeroKet n)) := by
        simp [act, Matrix.mulVec_mulVec]
      rw [hact, ih (by omega)]
      exact step_level x ⟨k, by omega⟩

private lemma ordered_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (U : Fin n → Matrix ι ι ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup ι ℂ) :
    orderedProd U ∈ Matrix.unitaryGroup ι ℂ := by
  unfold orderedProd
  apply list_prod_mem
  intro A hA
  have ha : A ∈ List.ofFn U := List.mem_reverse.mp hA
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
  exact hU k

private lemma sign_unitary (n : ℕ) (x : Fin (2^n) → ℝ) :
    Matrix.diagonal (fun z : Qubits n => if x (bitsEquivFin n z) < 0 then (-1 : ℂ) else 1) ∈
      Matrix.unitaryGroup (Qubits n) ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff.mpr
  change _ * (Matrix.diagonal _).conjTranspose = _
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst b; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    by_cases h : x (bitsEquivFin n a) < 0 <;> simp [h]
  · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

theorem solution (n : ℕ) (hn : 1 ≤ n) (x : Fin (2 ^ n) → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) :
    alg4Unitary n x ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧
      act (alg4Unitary n x) (zeroKet n) =
        padState n (normalizedVec (WithLp.toLp 2 fun j => (x j : ℂ))) := by
  classical
  constructor
  · exact mul_mem (sign_unitary n x) (ordered_unitary _ (step_unitary x))
  · have hnorm : ‖(WithLp.toLp 2 fun j => (x j : ℂ))‖ = 1 := by
      have hsq : ‖(WithLp.toLp 2 fun j => (x j : ℂ))‖^2 = 1 := by
        simpa [EuclideanSpace.norm_sq_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hx
      nlinarith [norm_nonneg (WithLp.toLp 2 fun j => (x j : ℂ))]
    have hP : act (orderedProd (alg4Step n x)) (zeroKet n) = levelState n x n := by
      simpa using product_level n x hx n (le_refl _)
    have hm (A B : Matrix (Qubits n) (Qubits n) ℂ) :
        act (A*B) (zeroKet n) = act A (act B (zeroKet n)) := by
      simp [act, Matrix.mulVec_mulVec]
    rw [alg4Unitary, hm, hP]
    apply PiLp.ext
    intro z
    have ht : tailZero n z := by intro a ha; omega
    have hlt : bitsToNat z < 2^n := by rw [← bitsEquivFin_apply]; exact (bitsEquivFin n z).isLt
    have hidx : (⟨bitsToNat z,hlt⟩ : Fin (2^n)) = bitsEquivFin n z := by
      apply Fin.ext; exact (bitsEquivFin_apply z).symm
    simp only [act, Matrix.mulVec_diagonal, PiLp.toLp_apply, levelState, if_pos ht,
      tree_leaf, Real.sqrt_sq_eq_abs, padState, normalizedVec, hnorm, inv_one,
      Complex.ofReal_one, one_smul, dif_pos hlt, hidx]
    split_ifs with h
    · rw [abs_of_neg h]; push_cast; ring
    · rw [abs_of_nonneg (le_of_not_gt h)]; simp
