-- Prove2me | solution 1 for ZipfLaw.monkey_typing_power_law
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:47.124486+00:00
-- url     : https://prove2.me/submissions/5a6a3d11-566b-4e36-bc62-0081e57fa7f1

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma zipf_geometric_count (m n : ℕ) (hm : 2 ≤ m) :
    (∑ j ∈ Finset.range n, m ^ j) ≤ m ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc
      _ ≤ m ^ n + m ^ n := Nat.add_le_add_right ih _
      _ ≤ m ^ n * m := by simpa [Nat.mul_two] using Nat.mul_le_mul_left (m ^ n) hm

theorem solution (m : ℕ) (hm : 2 ≤ m) (q : ℝ) (hq : 0 < q) (hmq : (m : ℝ) * q < 1)
    (e : ℕ → List (Fin m)) (he_inj : Function.Injective e)
    (he_range : Set.range e = {w | w ≠ []})
    (he_sorted : Antitone (fun r => monkeyWordProb m q (e r))) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ r : ℕ,
      C₁ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) ≤ monkeyWordProb m q (e r) ∧
        monkeyWordProb m q (e r) ≤ C₂ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) := by
  classical
  have hmreal : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hmpos : (0 : ℝ) < m := lt_trans zero_lt_one hmreal
  have hq1 : q < 1 := by nlinarith
  have hS : 0 < 1 - (m : ℝ) * q := by linarith
  have hnonempty (i : ℕ) : e i ≠ [] := by
    have hi : e i ∈ Set.range e := ⟨i, rfl⟩
    rw [he_range] at hi
    exact hi
  refine ⟨q * (1 - m * q), (1 - m * q) / q, by positivity, by positivity, ?_⟩
  intro r
  let L := (e r).length
  have hL : 1 ≤ L := by
    have := hnonempty r
    simpa only [L, List.length_pos_iff, Nat.succ_le_iff] using List.length_pos_iff.mpr this
  have hlength (i : ℕ) (hi : i ≤ r) : (e i).length ≤ L := by
    have hprob := he_sorted hi
    unfold monkeyWordProb at hprob
    have hpow : q ^ L ≤ q ^ (e i).length := (mul_le_mul_iff_left₀ hS).mp hprob
    exact (pow_le_pow_iff_right_of_lt_one₀ hq hq1).mp hpow
  let T := (Finset.range (r + 1)).image e
  have hT : T.card = r + 1 := by
    simp [T, Finset.card_image_of_injective, he_inj]
  have hmap : (T : Set (List (Fin m))).MapsTo List.length (Finset.range (L + 1)) := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
    exact Finset.mem_range.mpr (by have := hlength i (by have := Finset.mem_range.mp hi; omega); omega)
  have hupper : r + 1 ≤ m ^ (L + 1) := by
    calc
      r + 1 = T.card := hT.symm
      _ = ∑ j ∈ Finset.range (L + 1), (T.filter (fun w => w.length = j)).card :=
        Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ j ∈ Finset.range (L + 1), m ^ j := by
        apply Finset.sum_le_sum
        intro j _
        simpa using (Finset.card_filter_length_eq_le (T := T) (s := j))
      _ ≤ m ^ (L + 1) := zipf_geometric_count m (L + 1) hm
  have hlower : m ^ (L - 1) ≤ r + 1 := by
    by_cases hn : L - 1 = 0
    · simp [hn]
    · let n := L - 1
      have hnpos : 0 < n := by omega
      have hnL : n < L := by omega
      have hex (v : Fin n → Fin m) : ∃ i : ℕ, e i = List.ofFn v := by
        apply Set.mem_range.mp
        rw [he_range]
        intro hnil
        have hlen := congrArg List.length hnil
        simp only [List.length_ofFn, List.length_nil] at hlen
        omega
      let idx (v : Fin n → Fin m) : ℕ := Classical.choose (hex v)
      have heq (v : Fin n → Fin m) : e (idx v) = List.ofFn v := Classical.choose_spec (hex v)
      have hidx (v : Fin n → Fin m) : idx v < r + 1 := by
        by_contra hbad
        have hprob := he_sorted (show r ≤ idx v by omega)
        unfold monkeyWordProb at hprob
        change q ^ (e (idx v)).length * (1 - m * q) ≤ q ^ L * (1 - m * q) at hprob
        rw [heq, List.length_ofFn] at hprob
        have hstrict := mul_lt_mul_of_pos_right (pow_right_strictAnti₀ hq hq1 hnL) hS
        change q ^ n * (1 - m * q) ≤ q ^ L * (1 - m * q) at hprob
        linarith
      let g (v : Fin n → Fin m) : Fin (r + 1) := ⟨idx v, hidx v⟩
      have hg : Function.Injective g := by
        intro v w hvw
        apply List.ofFn_injective
        have hi : idx v = idx w := congrArg Fin.val hvw
        rw [← heq v, ← heq w, hi]
      simpa [n] using Fintype.card_le_of_injective g hg
  have hlower' : m ^ L ≤ m * (r + 1) := by
    calc
      m ^ L = m ^ (L - 1) * m := by rw [← pow_succ, Nat.sub_add_cancel hL]
      _ ≤ (r + 1) * m := Nat.mul_le_mul_right m hlower
      _ = m * (r + 1) := Nat.mul_comm _ _
  have hupper_real : (r : ℝ) + 1 ≤ (m : ℝ) ^ (L + 1) := by exact_mod_cast hupper
  have hlower_real : (m : ℝ) ^ L ≤ (m : ℝ) * ((r : ℝ) + 1) := by exact_mod_cast hlower'
  have hlog : -Real.logb (m : ℝ) (1 / q) = Real.logb (m : ℝ) q := by
    simp [one_div, Real.logb_inv]
  have hb : Real.logb (m : ℝ) q ≤ 0 := (Real.logb_neg hmreal hq hq1).le
  have hpower (n : ℕ) : ((m : ℝ) ^ n) ^ Real.logb (m : ℝ) q = q ^ n := by
    rw [← Real.rpow_pow_comm hmpos.le, Real.rpow_logb hmpos (ne_of_gt hmreal) hq]
  have hup := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (r : ℝ) + 1) hupper_real hb
  rw [hpower, pow_succ] at hup
  have hlo := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (m : ℝ) ^ L) hlower_real hb
  rw [hpower, Real.mul_rpow hmpos.le (by positivity),
    Real.rpow_logb hmpos (ne_of_gt hmreal) hq] at hlo
  rw [hlog]
  unfold monkeyWordProb
  change q * (1 - m * q) * ((r : ℝ) + 1) ^ Real.logb (m : ℝ) q ≤
      q ^ L * (1 - m * q) ∧
    q ^ L * (1 - m * q) ≤ (1 - m * q) / q * ((r : ℝ) + 1) ^ Real.logb (m : ℝ) q
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hlo hS.le]
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq).mpr
    nlinarith [mul_le_mul_of_nonneg_right hup hS.le]

#print axioms solution
