-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HessCCompPluri_fderiv_fderiv_comp_apply_52a7820e256e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:59.343361+00:00
-- url     : https://prove2.me/submissions/9afef233-1f43-44d7-9b7e-91831c764c86

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHessCCompPluri
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHessCCompPluri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace HessCCompPluri
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ} {L : E → ℝ} {z : E} (hF : ContDiffAt ℝ 2 F (L z)) (hL : ContDiffAt ℝ 2 L z)
    (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w => F (L w))) z v u =
      deriv (deriv F) (L z) * (fderiv ℝ L z v * fderiv ℝ L z u) +
        deriv F (L z) * fderiv ℝ (fderiv ℝ L) z v u := by
  have hL2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 L w := hL.eventually (by simp)
  have hF2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 F (L w) :=
    hL.continuousAt.tendsto.eventually (hF.eventually (by simp))
  have heq : fderiv ℝ (fun w => F (L w)) =ᶠ[𝓝 z] fun w => deriv F (L w) • fderiv ℝ L w := by
    filter_upwards [hL2, hF2] with w hw hFw
    exact ((hFw.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt w
      (hw.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hdF : DifferentiableAt ℝ (deriv F) (L z) := by
    have h1 := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact h1.clm_apply (differentiableAt_const (1 : ℝ))
  have hdL : DifferentiableAt ℝ (fderiv ℝ L) z :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun w => deriv F (L w)) (deriv (deriv F) (L z) • fderiv ℝ L z) z :=
    hdF.hasDerivAt.comp_hasFDerivAt z (hL.differentiableAt (by norm_num)).hasFDerivAt
  have hs : HasFDerivAt (fun w => deriv F (L w) • fderiv ℝ L w)
      (deriv F (L z) • fderiv ℝ (fderiv ℝ L) z +
        (deriv (deriv F) (L z) • fderiv ℝ L z).smulRight (fderiv ℝ L z)) z :=
    hc.smul hdL.hasFDerivAt
  rw [heq.fderiv_eq, hs.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring
end HessCCompPluri
end GroundTheory.Heights₂.Heights
