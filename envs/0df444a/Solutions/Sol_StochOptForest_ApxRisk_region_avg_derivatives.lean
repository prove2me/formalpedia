-- Prove2me | solution 1 for StochOptForest.ApxRisk.region_avg_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:54:00.449794+00:00
-- url     : https://prove2.me/submissions/02a038eb-ec81-4741-b598-e565ebebeba1

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

open MeasureTheory StochOptForest.ApxRisk

namespace SOFRad

variable {p d : ℕ}

lemma grad_C1 {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  exact (InnerProductSpace.toDual ℝ (Ed d)).symm.contDiff.comp h1

lemma hess_cont {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (hess f) :=
  (grad_C1 hf).continuous_fderiv (by norm_num)

lemma fderiv_eq_toDual (f : Ed d → ℝ) (z : Ed d) :
    fderiv ℝ f z = InnerProductSpace.toDual ℝ (Ed d) (gradient f z) := by
  simp [gradient]

lemma cont_of_lip {E : Type*} [NormedAddCommGroup E] (g : Xp p → E) (L : ℝ)
    (h : ∀ x x', ‖g x - g x'‖ ≤ L * ‖x - x'‖) : Continuous g := by
  have : LipschitzWith (Real.toNNReal L) g := by
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖g x - g x'‖ ≤ L * ‖x - x'‖ := h x x'
      _ ≤ (Real.toNNReal L : ℝ) * ‖x - x'‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _)
  exact this.continuous

/-- Local uniform bound for a family that is `L`-Lipschitz in `x` on a bounded region. -/
lemma loc_bound {E : Type*} [NormedAddCommGroup E] (μ : Measure (Xp p)) (R : Set (Xp p))
    (hR : MeasurableSet R) (ρ : ℝ) (hρ : R ⊆ Metric.closedBall 0 ρ) (L : ℝ)
    (Ψ : Xp p → Ed d → E) (hL : ∀ z x x', ‖Ψ x z - Ψ x' z‖ ≤ L * ‖x - x'‖)
    (h0 : Continuous (Ψ 0)) (z0 : Ed d) :
    ∃ K, ∀ᵐ x ∂(μ.restrict R), ∀ z ∈ Metric.ball z0 1, ‖Ψ x z‖ ≤ K := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall z0 1).exists_bound_of_continuousOn h0.continuousOn
  refine ⟨C + |L| * ρ, ?_⟩
  filter_upwards [ae_restrict_mem hR] with x hx z hz
  have h1 := hC z (Metric.ball_subset_closedBall hz)
  have h2 := hL z x 0
  have h3 : ‖x‖ ≤ ρ := by
    have := hρ hx; rwa [Metric.mem_closedBall, dist_zero_right] at this
  rw [sub_zero] at h2
  have h4 : L * ‖x‖ ≤ |L| * ρ :=
    (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg L))
  calc ‖Ψ x z‖ = ‖(Ψ x z - Ψ 0 z) + Ψ 0 z‖ := by rw [sub_add_cancel]
    _ ≤ ‖Ψ x z - Ψ 0 z‖ + ‖Ψ 0 z‖ := norm_add_le _ _
    _ ≤ C + |L| * ρ := by linarith

lemma int_hasFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure (Xp p)) [IsFiniteMeasure ν] (Φ : Xp p → Ed d → E)
    (Φ' : Xp p → Ed d → (Ed d →L[ℝ] E))
    (hc : ∀ z, Continuous fun x => Φ x z) (hc' : ∀ z, Continuous fun x => Φ' x z)
    (hder : ∀ x z, HasFDerivAt (Φ x) (Φ' x z) z)
    (hb : ∀ z0 : Ed d, ∃ K, ∀ᵐ x ∂ν, ∀ z ∈ Metric.ball z0 1, ‖Φ x z‖ ≤ K)
    (hb' : ∀ z0 : Ed d, ∃ K, ∀ᵐ x ∂ν, ∀ z ∈ Metric.ball z0 1, ‖Φ' x z‖ ≤ K) (z0 : Ed d) :
    HasFDerivAt (fun z => ∫ x, Φ x z ∂ν) (∫ x, Φ' x z0 ∂ν) z0 := by
  obtain ⟨K, hK⟩ := hb z0
  obtain ⟨K', hK'⟩ := hb' z0
  have hint : Integrable (fun x => Φ x z0) ν :=
    Integrable.of_bound (hc z0).aestronglyMeasurable K
      (hK.mono fun x hx => hx z0 (Metric.mem_ball_self one_pos))
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball z0 1)
    (bound := fun _ => K') (Metric.ball_mem_nhds z0 one_pos)
    (Filter.Eventually.of_forall fun z => (hc z).aestronglyMeasurable) hint
    (hc' z0).aestronglyMeasurable hK' (integrable_const K')
    (ae_of_all _ fun x z _ => hder x z)

lemma int_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure (Xp p)) [IsFiniteMeasure ν] (Φ : Xp p → Ed d → E)
    (hc : ∀ z, Continuous fun x => Φ x z) (hcz : ∀ x, Continuous (Φ x))
    (hb : ∀ z0 : Ed d, ∃ K, ∀ᵐ x ∂ν, ∀ z ∈ Metric.ball z0 1, ‖Φ x z‖ ≤ K) :
    Continuous fun z => ∫ x, Φ x z ∂ν := by
  refine continuous_iff_continuousAt.2 fun z0 => ?_
  obtain ⟨K, hK⟩ := hb z0
  refine continuousAt_of_dominated (bound := fun _ => K)
    (Filter.Eventually.of_forall fun z => (hc z).aestronglyMeasurable) ?_ (integrable_const K)
    (ae_of_all _ fun x => (hcz x).continuousAt)
  filter_upwards [Metric.ball_mem_nhds z0 one_pos] with z hz
  exact hK.mono fun x hx => hx z hz

end SOFRad

open SOFRad

theorem solution {p d : ℕ} (μ : Measure (Xp p)) [IsProbabilityMeasure μ]
    (cbar : Xp p → Ed d → ℝ) (L : ℝ) (hC2 : ∀ x, ContDiff ℝ 2 (cbar x))
    (hLip : XLipschitz cbar L) (R : Set (Xp p)) (hR : MeasurableSet R)
    (hRb : Bornology.IsBounded R) (hpos : 0 < μ R) :
    ContDiff ℝ 2 (regionAvg μ cbar R) ∧
    (∀ z, gradient (regionAvg μ cbar R) z = (μ R).toReal⁻¹ • ∫ x in R, gradient (cbar x) z ∂μ) ∧
    (∀ z, hess (regionAvg μ cbar R) z = (μ R).toReal⁻¹ • ∫ x in R, hess (cbar x) z ∂μ) := by
  obtain ⟨ρ, hρ⟩ := hRb.subset_closedBall 0
  set ν := μ.restrict R with hν
  set T := InnerProductSpace.toDual ℝ (Ed d) with hT
  -- Lipschitz bounds in `x`
  have hL0 : ∀ z x x', ‖cbar x z - cbar x' z‖ ≤ L * ‖x - x'‖ := fun z x x' => by
    rw [Real.norm_eq_abs]; exact (hLip z x x').1
  have hL1 : ∀ z x x', ‖gradient (cbar x) z - gradient (cbar x') z‖ ≤ L * ‖x - x'‖ :=
    fun z x x' => (hLip z x x').2.1
  have hL2 : ∀ z x x', ‖hess (cbar x) z - hess (cbar x') z‖ ≤ L * ‖x - x'‖ :=
    fun z x x' => (hLip z x x').2.2
  have hL1' : ∀ z x x', ‖fderiv ℝ (cbar x) z - fderiv ℝ (cbar x') z‖ ≤ L * ‖x - x'‖ := by
    intro z x x'
    rw [fderiv_eq_toDual, fderiv_eq_toDual, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hL1 z x x'
  -- continuity in `x` and `z`
  have hc0 : ∀ z, Continuous fun x => cbar x z := fun z => cont_of_lip _ L (hL0 z)
  have hc1 : ∀ z, Continuous fun x => gradient (cbar x) z := fun z => cont_of_lip _ L (hL1 z)
  have hc1' : ∀ z, Continuous fun x => fderiv ℝ (cbar x) z := fun z => cont_of_lip _ L (hL1' z)
  have hc2 : ∀ z, Continuous fun x => hess (cbar x) z := fun z => cont_of_lip _ L (hL2 z)
  -- local bounds
  have hb0 := loc_bound μ R hR ρ hρ L (fun x z => cbar x z) hL0 (hC2 0).continuous
  have hb1 := loc_bound μ R hR ρ hρ L (fun x z => gradient (cbar x) z) hL1 (grad_C1 (hC2 0)).continuous
  have hb1' := loc_bound μ R hR ρ hρ L (fun x z => fderiv ℝ (cbar x) z) hL1'
    ((hC2 0).continuous_fderiv (by norm_num))
  have hb2 := loc_bound μ R hR ρ hρ L (fun x z => hess (cbar x) z) hL2 (hess_cont (hC2 0))
  -- derivatives of the integrals
  set A : Ed d → ℝ := fun z => ∫ x, cbar x z ∂ν with hA
  set G : Ed d → Ed d := fun z => ∫ x, gradient (cbar x) z ∂ν with hG
  set Hm : Ed d → (Ed d →L[ℝ] Ed d) := fun z => ∫ x, hess (cbar x) z ∂ν with hHm
  have hAd : ∀ z, HasFDerivAt A (T (G z)) z := by
    intro z
    have := int_hasFDeriv ν (fun x z => cbar x z) (fun x z => fderiv ℝ (cbar x) z) hc0 hc1'
      (fun x z => ((hC2 x).differentiable (by norm_num) z).hasFDerivAt) hb0 hb1' z
    have e : ∫ x, fderiv ℝ (cbar x) z ∂ν = T (G z) := by
      simp_rw [fderiv_eq_toDual]
      exact (T.toContinuousLinearEquiv).integral_comp_comm _
    rw [e] at this
    exact this
  have hGd : ∀ z, HasFDerivAt G (Hm z) z := by
    intro z
    exact int_hasFDeriv ν (fun x z => gradient (cbar x) z) (fun x z => hess (cbar x) z) hc1 hc2
      (fun x z => (((grad_C1 (hC2 x)).differentiable (by norm_num)) z).hasFDerivAt) hb1 hb2 z
  have hHc : Continuous Hm :=
    int_cont ν (fun x z => hess (cbar x) z) hc2 (fun x => hess_cont (hC2 x)) hb2
  set c := (μ R).toReal with hc
  have hreg : regionAvg μ cbar R = fun z => c⁻¹ * A z := rfl
  have hfd : ∀ z, HasFDerivAt (regionAvg μ cbar R) (c⁻¹ • T (G z)) z := by
    intro z; rw [hreg]; exact (hAd z).const_mul c⁻¹
  have hgrad : ∀ z, gradient (regionAvg μ cbar R) z = c⁻¹ • G z := by
    intro z
    unfold gradient
    rw [(hfd z).fderiv, map_smul, LinearIsometryEquiv.symm_apply_apply]
  have hgradf : gradient (regionAvg μ cbar R) = fun z => c⁻¹ • G z := funext hgrad
  have hGs : ∀ z, HasFDerivAt (fun z => c⁻¹ • G z) (c⁻¹ • Hm z) z :=
    fun z => (hGd z).const_smul c⁻¹
  refine ⟨?_, hgrad, fun z => ?_⟩
  · -- `C²`
    have hG1 : ContDiff ℝ 1 G := by
      rw [contDiff_one_iff_fderiv]
      refine ⟨fun z => (hGd z).differentiableAt, ?_⟩
      have : fderiv ℝ G = Hm := funext fun z => (hGd z).fderiv
      rw [this]; exact hHc
    have hfd' : fderiv ℝ (regionAvg μ cbar R) = fun z => c⁻¹ • T (G z) :=
      funext fun z => (hfd z).fderiv
    have h2' : ContDiff ℝ 1 (fun z => T (G z)) := T.toContinuousLinearEquiv.contDiff.comp hG1
    have h2 : ContDiff ℝ 1 (fun z => c⁻¹ • T (G z)) := h2'.const_smul c⁻¹
    show ContDiff ℝ (1 + 1) (regionAvg μ cbar R)
    rw [contDiff_succ_iff_fderiv]
    refine ⟨fun z => (hfd z).differentiableAt, by simp, ?_⟩
    rw [hfd']; exact h2
  · show fderiv ℝ (gradient (regionAvg μ cbar R)) z = _
    rw [hgradf, (hGs z).fderiv]
