-- Prove2me | solution 1 for OptimisticPSRL.Concentration.proof_prop5_2_predictable_variance
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:08:07.1664+00:00
-- url     : https://prove2.me/submissions/54d2ad6f-ff8b-4414-8004-368f5d6955a7

import Mathlib
import Definitions.Def_OptimisticPSRL_Concentration_Setting

open MeasureTheory

namespace Aux_OPSRL_pv
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


lemma tail_split {S : ℕ} (p : Fin S → ℝ) (i : Fin S) : tail p i = p i + tailAfter p i := by
  unfold tail tailAfter
  rw [Finset.sum_filter, Finset.sum_filter]
  have : p i = ∑ j, if j = i then p j else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h.le, if_neg (ne_of_gt h), if_pos h]; ring
  · subst h; simp
  · rw [if_neg (not_le.mpr h), if_neg (ne_of_lt h), if_neg (not_lt.mpr h.le)]; ring

lemma diag {S : ℕ} (p h : Fin S → ℝ) (hp : IsProbVec p) (i : Fin S) :
    ∑ k, p k * (Zcoord p h i k * Zcoord p h i k) = cCoef p h i ^ 2 * gammaCoef p i := by
  have hpt : ∀ k, Zcoord p h i k * Zcoord p h i k = cCoef p h i ^ 2 *
      ((if k = i then 1 else 0) * (1 - 2 * yRatio p i) + yRatio p i ^ 2 * (if i ≤ k then 1 else 0)) := by
    intro k
    unfold Zcoord
    split_ifs
    all_goals first
      | (exfalso; simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, not_le] at *; omega)
      | ring
  simp_rw [hpt]
  have e1 : ∑ k, p k * (cCoef p h i ^ 2 * ((if k = i then (1:ℝ) else 0) * (1 - 2 * yRatio p i) +
      yRatio p i ^ 2 * (if i ≤ k then (1:ℝ) else 0))) =
      cCoef p h i ^ 2 * ((1 - 2 * yRatio p i) * ∑ k, p k * (if k = i then (1:ℝ) else 0) +
        yRatio p i ^ 2 * ∑ k, p k * (if i ≤ k then (1:ℝ) else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have e2 : ∑ k, p k * (if k = i then (1:ℝ) else 0) = p i := by simp
  have e3 : ∑ k, p k * (if i ≤ k then (1:ℝ) else 0) = tail p i := by
    unfold tail
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  rw [e1, e2, e3]
  have hA0 : 0 ≤ tailAfter p i := Finset.sum_nonneg (fun j _ => hp.1 j)
  have hT := tail_split p i
  unfold gammaCoef yRatio
  by_cases ht : tail p i = 0
  · have hp0 : p i = 0 := by linarith [hp.1 i]
    rw [ht, hp0]; simp
  · rw [hT] at ht ⊢
    field_simp
    ring

end Aux_OPSRL_pv

open OptimisticPSRL.Concentration in
theorem solution {S : ℕ} (n : ℕ) (p h : Fin S → ℝ)
    (hp : IsProbVec p) :
    ∑ _t : Fin n, ∫ x, (∑ i, Zcoord p h i x) ^ 2 ∂(cat p) =
      ∑ i, cCoef p h i ^ 2 * n * gammaCoef p i := by
  have hE2 : ∀ i j, i ≠ j → ∑ k, p k * (Zcoord p h i k * Zcoord p h j k) = 0 := by
    intro i j hij
    rw [← Aux_OPSRL_pv.int_cat p hp.1]
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact Aux_OPSRL_pv.key p h hp i j hlt
    · rw [← Aux_OPSRL_pv.key p h hp j i hlt]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hE : ∫ x, (∑ i, Zcoord p h i x) ^ 2 ∂(cat p) = ∑ i, cCoef p h i ^ 2 * gammaCoef p i := by
    rw [Aux_OPSRL_pv.int_cat p hp.1]
    have hk : ∀ k, p k * (∑ i, Zcoord p h i k) ^ 2 =
        ∑ i, ∑ j, p k * (Zcoord p h i k * Zcoord p h j k) := by
      intro k
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    simp_rw [hk]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i (fun j _ hj => hE2 i j (Ne.symm hj)) (by simp)]
    exact Aux_OPSRL_pv.diag p h hp i
  rw [hE, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
