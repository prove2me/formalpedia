-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___symm_toLp_df79e3edb4b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:28.533574+00:00
-- url     : https://prove2.me/submissions/550cdcc2-4c82-4caa-bcbd-048a8150a673

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___apply_2484824798c0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {m : E → ℂ} {C s t : ℝ}
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution (ψ : 𝓢(E, F)) :
    (besselₗᵢ s).symm (ψ.toLp 2) =
      ofSchwartz s (SchwartzMap.fourierMultiplierCLM F (weight (-s)) ψ) := by
  rw [LinearIsometryEquiv.symm_apply_eq, besselₗᵢ_apply]
  apply toTemperedDistribution_injective
  simp only
  rw [toDistribution_bessel, toDistribution_ofSchwartz, Lp.toTemperedDistribution_toLp_eq,
    ← fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth _),
    ← besselPotential_eq_fourierMultiplierCLM, besselPotential_besselPotential_apply]
  simp
end GroundTheory.Automorphic.Sobolev.SobolevSpace
