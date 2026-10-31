-- Prove2me | solution 1 for StochOptForest.ApxRisk.fnorm_le_lip_diam
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:42:44.552971+00:00
-- url     : https://prove2.me/submissions/48d172f4-6f95-4270-8dae-159d73dbd65e

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model


import Theorems.Thm_StochOptForest_ApxRisk_region_avg_derivatives


open MeasureTheory StochOptForest.ApxRisk

namespace SOFFnorm

lemma grad_sub {d : ℕ} {f g : Ed d → ℝ} {z : Ed d} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    gradient (fun w => f w - g w) z = gradient f z - gradient g z := by
  unfold gradient
  rw [fderiv_fun_sub hf hg, map_sub]

lemma diff_grad {d : ℕ} {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) : Differentiable ℝ (gradient f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h2 : ContDiff ℝ 1 (fun z => (InnerProductSpace.toDual ℝ (Ed d)).symm (fderiv ℝ f z)) :=
    (InnerProductSpace.toDual ℝ (Ed d)).symm.contDiff.comp h1
  exact h2.differentiable (by norm_num)

lemma hess_sub {d : ℕ} {f g : Ed d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Ed d) :
    hess (fun w => f w - g w) z = hess f z - hess g z := by
  have e : gradient (fun w => f w - g w) = fun w => gradient f w - gradient g w := by
    funext w
    exact grad_sub ((hf.differentiable (by norm_num)) w) ((hg.differentiable (by norm_num)) w)
  unfold hess
  rw [e, fderiv_fun_sub ((diff_grad hf) z) ((diff_grad hg) z)]

lemma cont_of_lip {p : ℕ} {E : Type*} [NormedAddCommGroup E] (g : Xp p → E) (L : ℝ)
    (h : ∀ x x', ‖g x - g x'‖ ≤ L * ‖x - x'‖) : Continuous g := by
  have : LipschitzWith (Real.toNNReal L) g := by
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖g x - g x'‖ ≤ L * ‖x - x'‖ := h x x'
      _ ≤ (Real.toNNReal L : ℝ) * ‖x - x'‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _)
  exact this.continuous

lemma intOn_of_bdd {p : ℕ} {E : Type*} [NormedAddCommGroup E]
    (μ : Measure (Xp p)) [IsProbabilityMeasure μ] (g : Xp p → E) (hg : Continuous g)
    (R : Set (Xp p)) (hR : MeasurableSet R) (M : ℝ) (hb : ∀ x ∈ R, ‖g x‖ ≤ M) :
    IntegrableOn g R μ := by
  refine Measure.integrableOn_of_bounded (M := M) (measure_lt_top μ R).ne
    hg.aestronglyMeasurable ?_
  rw [ae_restrict_iff' hR]
  exact Filter.Eventually.of_forall hb

/-- Averaging a continuous function that stays within `K` of `v` on `R` stays within `K` of `v`. -/
lemma avg_sub_le {p : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (Xp p)) [IsProbabilityMeasure μ] (g : Xp p → E) (hg : Continuous g)
    (R : Set (Xp p)) (hR : MeasurableSet R) (hpos : 0 < μ R) (v : E) (K : ℝ)
    (hb : ∀ x ∈ R, ‖g x - v‖ ≤ K) :
    ‖(μ R).toReal⁻¹ • (∫ x in R, g x ∂μ) - v‖ ≤ K := by
  have hfin : μ R < ⊤ := measure_lt_top μ R
  have hc : 0 < (μ R).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hint : IntegrableOn g R μ := by
    refine Measure.integrableOn_of_bounded (M := ‖v‖ + K) hfin.ne
      hg.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hR]
    refine Filter.Eventually.of_forall fun x hx => ?_
    calc ‖g x‖ = ‖(g x - v) + v‖ := by rw [sub_add_cancel]
      _ ≤ ‖g x - v‖ + ‖v‖ := norm_add_le _ _
      _ ≤ ‖v‖ + K := by linarith [hb x hx]
  have e1 : ∫ x in R, (g x - v) ∂μ = (∫ x in R, g x ∂μ) - (μ R).toReal • v := by
    rw [integral_sub hint (integrable_const v), setIntegral_const, measureReal_def]
  have e2 : (μ R).toReal⁻¹ • (∫ x in R, g x ∂μ) - v
      = (μ R).toReal⁻¹ • ∫ x in R, (g x - v) ∂μ := by
    rw [e1, smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  have h3 := norm_setIntegral_le_of_norm_le_const hfin hb
  rw [measureReal_def] at h3
  calc (μ R).toReal⁻¹ * ‖∫ x in R, (g x - v) ∂μ‖ ≤ (μ R).toReal⁻¹ * (K * (μ R).toReal) :=
        mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hc).le
    _ = K := by field_simp

end SOFFnorm

open SOFFnorm

lemma two_avg {p : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (Xp p)) [IsProbabilityMeasure μ] (g : Xp p → E) (hg : Continuous g)
    (R0 Rj : Set (Xp p)) (hR0 : MeasurableSet R0) (hRj : MeasurableSet Rj) (hsub : Rj ⊆ R0)
    (hpos : 0 < μ Rj) (K : ℝ) (hb : ∀ x ∈ R0, ∀ x' ∈ R0, ‖g x - g x'‖ ≤ K) :
    ‖(μ Rj).toReal⁻¹ • (∫ x in Rj, g x ∂μ) - (μ R0).toReal⁻¹ • (∫ x in R0, g x ∂μ)‖ ≤ K := by
  have hpos0 : 0 < μ R0 := lt_of_lt_of_le hpos (measure_mono hsub)
  refine avg_sub_le μ g hg Rj hRj hpos _ K fun x hx => ?_
  rw [norm_sub_rev]
  exact avg_sub_le μ g hg R0 hR0 hpos0 (g x) K fun x' hx' => hb x' hx' x (hsub hx)

theorem solution {p d : ℕ} (μ : Measure (Xp p)) [IsProbabilityMeasure μ]
    (cbar : Xp p → Ed d → ℝ) (L : ℝ) (hC2 : ∀ x, ContDiff ℝ 2 (cbar x))
    (hLip : XLipschitz cbar L) (R0 Rj : Set (Xp p)) (hR0 : MeasurableSet R0)
    (hRj : MeasurableSet Rj) (hsub : Rj ⊆ R0) (hR0b : Bornology.IsBounded R0)
    (hpos : 0 < μ Rj) :
    FNormLE (fun z => regionAvg μ cbar Rj z - regionAvg μ cbar R0 z) (L * Metric.diam R0) := by
  have hpos0 : 0 < μ R0 := lt_of_lt_of_le hpos (measure_mono hsub)
  have hpair : ∀ x ∈ R0, ∀ x' ∈ R0, L * ‖x - x'‖ ≤ L * Metric.diam R0 := by
    intro x hx x' hx'
    rcases le_or_gt 0 L with hL | hL
    · rw [← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem hR0b hx hx') hL
    · have hss : R0.Subsingleton := by
        intro a ha b hb
        have h1 := (hLip 0 a b).1
        have h2 : 0 ≤ L * ‖a - b‖ := (abs_nonneg _).trans h1
        have h3 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
        exact sub_eq_zero.mp (norm_le_zero_iff.mp h3)
      rw [Metric.diam_subsingleton hss, hss hx hx', sub_self, norm_zero]
  have hcv : ∀ z, Continuous fun x => cbar x z := fun z =>
    cont_of_lip (fun x => cbar x z) L (fun x x' => by rw [Real.norm_eq_abs]; exact (hLip z x x').1)
  have hcg : ∀ z, Continuous fun x => gradient (cbar x) z := fun z =>
    cont_of_lip (fun x => gradient (cbar x) z) L (fun x x' => (hLip z x x').2.1)
  have hch : ∀ z, Continuous fun x => hess (cbar x) z := fun z =>
    cont_of_lip (fun x => hess (cbar x) z) L (fun x x' => (hLip z x x').2.2)
  obtain ⟨hCj, hgj, hhj⟩ := region_avg_derivatives μ cbar L hC2 hLip Rj hRj
    (hR0b.subset hsub) hpos
  obtain ⟨hC0, hg0, hh0⟩ := region_avg_derivatives μ cbar L hC2 hLip R0 hR0 hR0b hpos0
  intro z
  refine ⟨?_, ?_, ?_⟩
  · have h := two_avg μ (fun x => cbar x z) (hcv z) R0 Rj hR0 hRj hsub hpos (L * Metric.diam R0)
      (fun x hx x' hx' => by
        rw [Real.norm_eq_abs]; exact (hLip z x x').1.trans (hpair x hx x' hx'))
    rw [Real.norm_eq_abs, smul_eq_mul, smul_eq_mul] at h
    exact h
  · rw [grad_sub ((hCj.differentiable (by norm_num)) z) ((hC0.differentiable (by norm_num)) z),
      hgj z, hg0 z]
    exact two_avg μ (fun x => gradient (cbar x) z) (hcg z) R0 Rj hR0 hRj hsub hpos _
      (fun x hx x' hx' => (hLip z x x').2.1.trans (hpair x hx x' hx'))
  · rw [hess_sub hCj hC0, hhj z, hh0 z]
    exact two_avg μ (fun x => hess (cbar x) z) (hch z) R0 Rj hR0 hRj hsub hpos _
      (fun x hx x' hx' => (hLip z x x').2.2.trans (hpair x hx x' hx'))
