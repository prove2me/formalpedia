-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.integral_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:01.556533+00:00
-- url     : https://prove2.me/submissions/605d40d2-4734-49b4-b56a-8ce8e6b68872

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_map_PhiL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (U : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (H : (Sg ι A B → ℂ) → ℂ) (hH : Continuous H) :
    ∫ z, H z = ∫ z, H (Phi U z) := by
  have hL : Continuous (PhiL (A := A) (B := B) U) := LinearMap.continuous_of_finiteDimensional _
  conv_lhs => rw [← map_PhiL (A := A) (B := B) U hU1 hU2]
  rw [integral_map hL.measurable.aemeasurable hH.aestronglyMeasurable]
  rfl
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
