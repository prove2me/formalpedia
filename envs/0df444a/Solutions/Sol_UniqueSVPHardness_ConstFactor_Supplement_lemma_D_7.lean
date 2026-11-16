-- Prove2me | solution 1 for UniqueSVPHardness.ConstFactor.Supplement.lemma_D_7
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:07:04.481684+00:00
-- url     : https://prove2.me/submissions/abaab5fc-667e-4b3c-8ece-659d1f090678

import Mathlib

set_option autoImplicit false
namespace UniqueSVPHardness.ConstFactor.Supplement

theorem lemma_D_7 (P : ℕ) [Fact P.Prime] (T : ℕ)
    (hP : 2 * (⌈((T : ℝ) + 1) * Real.logb 2 P⌉₊ + 1) ≤ P) :
    ∃ c : ZMod P → ℤ, c ≠ 0 ∧ (∀ w, c w = -1 ∨ c w = 0 ∨ c w = 1) ∧
      ∑ w, c w = 0 ∧
      (∀ j ≤ T, ∑ w : ZMod P, (c w : ZMod P) * w ^ j = 0) ∧
      ∑ w, c w ^ 2 ≤ 2 * ((⌈((T : ℝ) + 1) * Real.logb 2 P⌉₊ : ℤ) + 1) := by
  classical
  set m : ℕ := ⌈((T : ℝ) + 1) * Real.logb 2 P⌉₊ with hm
  have hPpos : 1 < P := (Fact.out : P.Prime).one_lt
  -- P^(T+1) ≤ 2^m
  have hpow : P ^ (T + 1) ≤ 2 ^ m := by
    have hle : ((T : ℝ) + 1) * Real.logb 2 P ≤ m := Nat.le_ceil _
    have hP0 : (0:ℝ) < P := by exact_mod_cast (by omega : 0 < P)
    have : ((P : ℝ)) ^ (T + 1) ≤ (2:ℝ) ^ m := by
      calc ((P : ℝ)) ^ (T + 1) = (2:ℝ) ^ (((T:ℝ) + 1) * Real.logb 2 P) := by
            rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hP0]
            rw [← Real.rpow_natCast]; push_cast; ring_nf
        _ ≤ (2:ℝ) ^ (m:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
        _ = (2:ℝ) ^ m := Real.rpow_natCast _ _
    exact_mod_cast this
  -- choose W of size m+1
  have hWc : m + 1 ≤ Fintype.card (ZMod P) := by rw [ZMod.card]; omega
  obtain ⟨W, -, hW⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod P))) (n := m + 1)
    (by rw [Finset.card_univ]; exact hWc)
  -- pigeonhole
  let F : Finset (ZMod P) → (Fin (T + 1) → ZMod P) := fun S j => ∑ w ∈ S, w ^ (j : ℕ)
  have hlt : (Finset.univ : Finset (Fin (T + 1) → ZMod P)).card < W.powerset.card := by
    rw [Finset.card_powerset, hW, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    calc P ^ (T + 1) ≤ 2 ^ m := hpow
      _ < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨S1, hS1, S2, hS2, hne, hF⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (f := F) (fun _ _ => Finset.mem_univ _)
  rw [Finset.mem_powerset] at hS1 hS2
  have hc1 : S1.card ≤ m + 1 := by have := Finset.card_le_card hS1; omega
  have hc2 : S2.card ≤ m + 1 := by have := Finset.card_le_card hS2; omega
  have hmom : ∀ j ≤ T, ∑ w ∈ S1, w ^ j = ∑ w ∈ S2, w ^ j := by
    intro j hj
    have := congrFun hF ⟨j, by omega⟩
    simpa [F] using this
  have hcard : S1.card = S2.card := by
    have h0 := hmom 0 (Nat.zero_le _)
    simp only [pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one] at h0
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h0
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  let c : ZMod P → ℤ := fun w => (if w ∈ S1 then 1 else 0) - (if w ∈ S2 then 1 else 0)
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    ext w
    have := congrFun h0 w
    simp only [c, Pi.zero_apply] at this
    by_cases h1 : w ∈ S1 <;> by_cases h2 : w ∈ S2 <;> simp_all
  · intro w
    simp only [c]
    by_cases h1 : w ∈ S1 <;> by_cases h2 : w ∈ S2 <;> simp [h1, h2]
  · simp only [c, Finset.sum_sub_distrib, Finset.sum_boole]
    simp [Finset.filter_mem_eq_inter, hcard]
  · intro j hj
    have : ∀ w : ZMod P, ((c w : ℤ) : ZMod P) * w ^ j =
        (if w ∈ S1 then w ^ j else 0) - (if w ∈ S2 then w ^ j else 0) := by
      intro w; simp only [c]
      by_cases h1 : w ∈ S1 <;> by_cases h2 : w ∈ S2 <;> simp [h1, h2]
    simp only [this, Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, hmom j hj, sub_self]
  · have hb : ∀ w : ZMod P, c w ^ 2 ≤ (if w ∈ S1 then 1 else 0) + (if w ∈ S2 then 1 else 0) := by
      intro w; simp only [c]
      by_cases h1 : w ∈ S1 <;> by_cases h2 : w ∈ S2 <;> simp [h1, h2]
    calc ∑ w, c w ^ 2 ≤ ∑ w : ZMod P, ((if w ∈ S1 then (1:ℤ) else 0) + (if w ∈ S2 then 1 else 0)) :=
          Finset.sum_le_sum (fun w _ => hb w)
      _ = (S1.card : ℤ) + S2.card := by
          rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
          simp [Finset.filter_mem_eq_inter]
      _ ≤ 2 * ((m : ℤ) + 1) := by omega

end UniqueSVPHardness.ConstFactor.Supplement

open UniqueSVPHardness.ConstFactor.Supplement in
theorem solution (P : ℕ) [Fact P.Prime] (T : ℕ)
    (hP : 2 * (⌈((T : ℝ) + 1) * Real.logb 2 P⌉₊ + 1) ≤ P) :
    ∃ c : ZMod P → ℤ, c ≠ 0 ∧ (∀ w, c w = -1 ∨ c w = 0 ∨ c w = 1) ∧
      ∑ w, c w = 0 ∧
      (∀ j ≤ T, ∑ w : ZMod P, (c w : ZMod P) * w ^ j = 0) ∧
      ∑ w, c w ^ 2 ≤ 2 * ((⌈((T : ℝ) + 1) * Real.logb 2 P⌉₊ : ℤ) + 1) :=
  UniqueSVPHardness.ConstFactor.Supplement.lemma_D_7 P T hP
