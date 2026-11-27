-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LEx2_A_mulF_one__3c7814d77c17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:20.223963+00:00
-- url     : https://prove2.me/submissions/87503c11-9cec-4a4b-8780-e34ec1daeb3a

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution (B : Base) {A : Type} (u : Fn B A) : mulF B (fun x => x ^ (0:ℝ)) u = u := by
  funext ω a; simp [mulF]
end Formalism.FourierDecayAlt.P.LEx2.A
