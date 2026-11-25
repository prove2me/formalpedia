-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LEx2_meas_th__13e6d05155eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:04.407687+00:00
-- url     : https://prove2.me/submissions/031e554b-b26d-470e-9a92-dc85d2e0cd5a

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (B : Base) (ε σ : ℝ) : Measurable fun ω => th ε σ (B.G ω) := by
  unfold th
  exact ((B.G_meas).div (B.G_meas.add_const ε)).pow_const σ
end Formalism.FourierDecayAlt.P.LEx2
