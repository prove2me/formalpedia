-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.lim_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:10.634898+00:00
-- url     : https://prove2.me/submissions/a363866f-8b61-4538-bc05-f1f04a52c39d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ExpCombine
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousCexpIp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_cexp_ip
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_gam
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_norm_cexp_neg_It
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_norm_gauss_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
set_option maxHeartbeats 1000000
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (ρ : E n → ℂ) (hρ : Integrable ρ) (t : ℝ) (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ)
    (C : ℂ) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ β, ψ β * (C * ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))))
      atTop (𝓝 (∫ β, ψ β * (C * ∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y))))) := by
  have hexp := continuous_cexp_ip (n := n) t
  have hbd : ∀ k y β, ‖ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))‖ ≤ ‖ρ y‖ := by
    intro k y β
    rw [norm_mul, norm_mul, norm_cexp_neg_It, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_gauss_le _ (hε k) y)
  have hcont : ∀ k, Continuous (fun β : E n => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))) := by
    intro k
    refine continuous_of_dominated (bound := fun y => ‖ρ y‖) ?_ ?_ hρ.norm ?_
    · intro β
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro β; exact Eventually.of_forall fun y => hbd k y β
    · exact Eventually.of_forall fun y => continuous_const.mul (hexp.comp (continuous_id.prodMk continuous_const))
  have hin : ∀ β : E n, Tendsto (fun k => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y)))
      atTop (𝓝 (∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y)))) := by
    intro β
    refine tendsto_integral_of_dominated_convergence (fun y => ‖ρ y‖) ?_ hρ.norm ?_ ?_
    · intro k
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro k; exact Eventually.of_forall fun y => hbd k y β
    · refine Eventually.of_forall fun y => ?_
      have h0 : Tendsto (fun k => -(((ε k * ip y y : ℝ)) : ℂ)) atTop (𝓝 0) := by
        have h := hε0.mul_const (ip y y)
        rw [zero_mul] at h
        have h' := ((Complex.continuous_ofReal.tendsto 0).comp h).neg
        simpa [Function.comp_def] using h'
      have hg : Tendsto (fun k => gam (ε k) y) atTop (𝓝 1) := by
        have := (Complex.continuous_exp.tendsto 0).comp h0
        simpa [gam, Function.comp_def] using this
      have := ((tendsto_const_nhds (x := ρ y)).mul hg).mul
        (tendsto_const_nhds (x := Complex.exp (-(Complex.I * t * ip β y))))
      simpa using this
  refine tendsto_integral_of_dominated_convergence (fun β => ‖ψ β‖ * (‖C‖ * ∫ y, ‖ρ y‖)) ?_
    (hψi.norm.mul_const _) ?_ ?_
  · intro k
    exact (hψc.mul (continuous_const.mul (hcont k))).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun β => ?_
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (norm_nonneg _)
    exact norm_integral_le_of_norm_le hρ.norm (Eventually.of_forall fun y => hbd k y β)
  · exact Eventually.of_forall fun β => tendsto_const_nhds.mul (tendsto_const_nhds.mul (hin β))
end PositivityTheory.Rg.Sw.WR.D.Moll
