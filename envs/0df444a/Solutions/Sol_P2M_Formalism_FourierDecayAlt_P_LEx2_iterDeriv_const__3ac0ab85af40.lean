-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LEx2_iterDeriv_const__3ac0ab85af40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:03.663954+00:00
-- url     : https://prove2.me/submissions/8b5eea15-fcff-48d1-997b-152523b996a4

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit

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
theorem _root_.solution (p : ℕ) (k t : ℝ) : iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
  cases p with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']
end Formalism.FourierDecayAlt.P.LEx2
