-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LEx1_meas_th__0b3f90443561
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:14.199284+00:00
-- url     : https://prove2.me/submissions/45fcbe4f-628e-473c-a86d-561ac55a38af

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_meas_th

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (B : Base) (ε σ : ℝ) : Measurable fun ω => th ε σ (B.G ω) := meas_th B ε σ
end Formalism.FourierDecayAlt.P.LEx1
