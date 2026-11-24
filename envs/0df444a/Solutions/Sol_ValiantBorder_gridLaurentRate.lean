-- Prove2me | solution 1 for ValiantBorder.gridLaurentRate
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:27:41.256795+00:00
-- url     : https://prove2.me/submissions/45869bfd-46e4-4a8c-8234-ff6ea8399ec4

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_priceAlternative
import Theorems.Thm_ValiantBorder_flatApproxRate
import Theorems.Thm_ValiantBorder_contractingApproxRate

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, sections “Tensors”,
“The metrics of the spectral points” and “Flat or contracting”, and Appendix N. Source:
`anthropics/formal-math` revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5, `vp-vnp/`, Apache-2.0. -/
open MvPolynomial Statement

private theorem thm_main_calculation (C : ℝ) : ∃ m₀ : ℕ, ∀ m ≥ m₀,
    C * Real.logb 2 m ^ (4 / 3 : ℝ) ≤ Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m) := by
  have ht : Filter.Tendsto (fun m : ℕ => Real.logb 2 m) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h0 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).bound
    (show (0 : ℝ) < Real.log 2 / (|C| + 1) by positivity)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 ((ht.eventually h0).and (ht.eventually_gt_atTop 2))
  refine ⟨m₀, fun m hm => ?_⟩
  obtain ⟨h1, hL⟩ := hm₀ m hm
  set L := Real.logb 2 m
  have hL0 : 0 < L := by linarith
  have hl : 0 < Real.logb 2 L := Real.logb_pos (by norm_num) (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at h1
  have h3 : (|C| + 1) * Real.logb 2 L ≤ L ^ (2 / 3 : ℝ) := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.logb, ← mul_div_assoc, div_le_iff₀ hlog]
    calc (|C| + 1) * Real.log L ≤ (|C| + 1) * (Real.log 2 / (|C| + 1) * L ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp
  rw [le_div_iff₀ hl]
  calc C * L ^ (4 / 3 : ℝ) * Real.logb 2 L = L ^ (4 / 3 : ℝ) * (C * Real.logb 2 L) := by ring
    _ ≤ L ^ (4 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hL0.le _)
        nlinarith [le_abs_self C]
    _ = L ^ 2 := by
        rw [← Real.rpow_add hL0, show (4 / 3 : ℝ) + 2 / 3 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem thm_allfields_exceeds {P : ℕ → ℕ → Prop}
    (h : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨c, hc, m₁, h⟩ := h
  obtain ⟨m₂, hm₂⟩ := thm_main_calculation (1 / (c * 1600 ^ 2))
  refine ⟨m₁ + m₂, fun m hm s hs => lt_of_le_of_lt ?_ (h m (by omega) s hs)⟩
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (hm₂ m (by omega)) hc.le).trans_eq (mul_div_assoc _ _ _).symm)
  field_simp

section
variable {F : Type*} [CommRing F]
noncomputable def laurentToSeries (F : Type*) [CommRing F] : LaurentPolynomial F →+* LaurentSeries F :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C
    { toFun := fun n => HahnSeries.single n.toAdd 1
      map_one' := rfl
      map_mul' := fun a b => by rw [HahnSeries.single_mul_single, toAdd_mul, one_mul] }
    fun _ _ => Commute.all _ _

/-- The series of a Laurent polynomial has the same coefficients. -/
@[simp] theorem coeff_laurentToSeries (x : LaurentPolynomial F) (i : ℤ) :
    (laurentToSeries F x).coeff i = x.coeff i := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, HahnSeries.coeff_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    classical
    rw [laurentToSeries, AddMonoidAlgebra.liftNCRingHom_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
    change a * (HahnSeries.single n (1 : F)).coeff i = _
    rw [HahnSeries.coeff_single]
    by_cases h : i = n
    · simp [h]
    · simp [h, Ne.symm h]

end
private theorem mapCircuit {R S : Type*} [CommSemiring R] [CommSemiring S] {V : Type}
    (φ : R →+* S) {f : MvPolynomial V R} {s : ℕ} (hf : Statement.Computes f s) :
    Statement.Computes (MvPolynomial.map φ f) s := by
  obtain ⟨g, steps, a, ha, rfl⟩ := hf
  refine ⟨fun j => MvPolynomial.map φ (g j), ?_, a, ha, rfl⟩
  intro k hk
  rcases steps k hk with ⟨i, h⟩ | ⟨c, h⟩ | ⟨i, hi, j, hj, h⟩ | ⟨i, hi, j, hj, h⟩
  · exact Or.inl ⟨i, by simp [h]⟩
  · exact Or.inr (Or.inl ⟨φ c, by simp [h]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by simp [h]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by simp [h]⟩))

theorem solution {K : Type} [Field K]
    {G : ∀ m, MvPolynomial (Fin m × Fin m) K} {κ : ℕ} (hG : ValiantBorder.GridComplete K G κ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (s : ℕ) (Q : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K)),
      Statement.Computes Q s →
      (∀ d, (∀ i : ℤ, i < 0 → (MvPolynomial.coeff d Q).coeff i = 0) ∧
        (MvPolynomial.coeff d Q).coeff 0 = MvPolynomial.coeff d (G m)) →
      (2 : ℝ) ^ ((Real.logb 2 m) ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨M, rate⟩ : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Statement.Approximates (G m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
    rcases ValiantBorder.priceAlternative K with h | h
    · obtain ⟨M, hm⟩ := ValiantBorder.flatApproxRate κ
      exact ⟨M, hm K h G hG⟩
    · exact thm_allfields_exceeds (ValiantBorder.contractingApproxRate h hG)
  refine ⟨M, fun m hm s Q hQ hs => rate m hm s ?_⟩
  refine ⟨MvPolynomial.map (laurentToSeries K) Q, mapCircuit _ hQ, fun d i hi => ?_⟩
  rw [coeff_map, coeff_laurentToSeries]
  rcases eq_or_lt_of_le hi with rfl | hneg
  · rw [if_pos rfl, (hs d).2]
  · rw [if_neg hneg.ne, (hs d).1 i hneg]
