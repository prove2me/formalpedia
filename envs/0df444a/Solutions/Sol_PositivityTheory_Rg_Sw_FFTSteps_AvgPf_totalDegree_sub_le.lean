-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AvgPf.totalDegree_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:06.357378+00:00
-- url     : https://prove2.me/submissions/41983e40-a2a8-4c45-97a8-5f583160108e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TotalDegreeLinear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousCoeffSub
import Theorems.Thm_UpperTheory_Reformulated_B_TotalDegreeLinear_main


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
variable {ι A B : Type} [Fintype ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AvgPf
theorem _root_.solution (g h : Matrix ι ι ℂ) (p : PV ι A B) : (sub g h p).totalDegree ≤ p.totalDegree :=
  _root_.UpperTheory.Reformulated.B.TotalDegreeLinear.main g h p
end PositivityTheory.Rg.Sw.FFTSteps.AvgPf
