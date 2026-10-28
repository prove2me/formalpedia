-- Prove2me | solution 1 for OptimisticPSRL.Concentration.proof_prop5_2_coordinates_uncorrelated
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:05:31.313872+00:00
-- url     : https://prove2.me/submissions/e84c6df8-e312-449b-9b46-fd3b0eeea940

import Mathlib
import Definitions.Def_OptimisticPSRL_Concentration_Setting

open MeasureTheory

namespace Aux_OPSRL_unc
open OptimisticPSRL.Concentration

lemma cat_single {S : ℕ} (p : Fin S → ℝ) (k : Fin S) :
    cat p {k} = ENNReal.ofReal (p k) := by
  simp only [cat, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · rw [Measure.dirac_apply_of_mem (Set.mem_singleton k), mul_one]
  · intro b _ hb
    rw [Measure.dirac_apply' _ (measurableSet_singleton k)]
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma int_cat {S : ℕ} (p : Fin S → ℝ) (hp : ∀ i, 0 ≤ p i) (f : Fin S → ℝ) :
    ∫ x, f x ∂(cat p) = ∑ k, p k * f k := by
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_eq_mul, measureReal_def, cat_single, ENNReal.toReal_ofReal (hp k)]

lemma key {S : ℕ} (p h : Fin S → ℝ) (hp : IsProbVec p) (a b : Fin S) (hab : a < b) :
    ∫ x, Zcoord p h a x * Zcoord p h b x ∂(cat p) = 0 := by
  have hpt : ∀ k, Zcoord p h a k * Zcoord p h b k =
      cCoef p h a * cCoef p h b * (-yRatio p a) *
        ((if k = b then 1 else 0) - yRatio p b * (if b ≤ k then 1 else 0)) := by
    intro k
    unfold Zcoord
    split_ifs
    all_goals first
      | (exfalso; simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, not_le] at *; omega)
      | ring
  rw [int_cat p hp.1]
  simp_rw [hpt]
  set C := cCoef p h a * cCoef p h b * (-yRatio p a)
  have e1 : ∑ k, p k * (C * ((if k = b then 1 else 0) - yRatio p b * (if b ≤ k then 1 else 0)))
      = C * (∑ k, p k * (if k = b then (1:ℝ) else 0)) -
        C * yRatio p b * ∑ k, p k * (if b ≤ k then (1:ℝ) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have e2 : ∑ k, p k * (if k = b then (1:ℝ) else 0) = p b := by simp
  have e3 : ∑ k, p k * (if b ≤ k then (1:ℝ) else 0) = tail p b := by
    unfold tail
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  have hle : p b ≤ tail p b := by
    unfold tail
    exact Finset.single_le_sum (fun j _ => hp.1 j) (by simp)
  have hkey : yRatio p b * tail p b = p b := by
    unfold yRatio
    by_cases ht : tail p b = 0
    · have : p b = 0 := le_antisymm (ht ▸ hle) (hp.1 b)
      rw [ht, this]; simp
    · field_simp
  rw [e1, e2, e3]
  linear_combination (-C) * hkey

end Aux_OPSRL_unc

open OptimisticPSRL.Concentration in
theorem solution {S : ℕ} (p h : Fin S → ℝ) (hp : IsProbVec p)
    (i j : Fin S) (hij : i ≠ j) :
    ∫ x, Zcoord p h i x * Zcoord p h j x ∂(cat p) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact Aux_OPSRL_unc.key p h hp i j hlt
  · rw [← Aux_OPSRL_unc.key p h hp j i hlt]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
