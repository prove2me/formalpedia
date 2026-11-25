-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AvgPf.map_star_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:58.205406+00:00
-- url     : https://prove2.me/submissions/95345e56-e48a-49b5-8344-c015f8d51dae

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TotalDegreeLinear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousCoeffSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PositivityTheory.Rg.Sw.FFTSteps.AvgPf
namespace PositivityTheory.Rg.Sw.FFTSteps.AvgPf
theorem _root_.solution {N : ℕ} (a b : Matrix (Fin N) (Fin N) ℂ) : (a * b).map star = a.map star * b.map star := by
  ext i j
  simp [Matrix.mul_apply]
end PositivityTheory.Rg.Sw.FFTSteps.AvgPf
