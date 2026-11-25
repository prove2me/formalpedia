-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AvgPf.continuous_toMK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:49.291424+00:00
-- url     : https://prove2.me/submissions/ee873f29-5652-45e3-a1a9-59acbc7d56bb

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
theorem _root_.solution (N : ℕ) : Continuous fun k : Formalism.REAL.KG (εT N) => Formalism.REAL.toMK k :=
  (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val
end PositivityTheory.Rg.Sw.FFTSteps.AvgPf
