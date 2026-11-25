-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LEx1_iterDeriv_const__d24bf99a7d59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:02.854175+00:00
-- url     : https://prove2.me/submissions/157f8c8e-b77a-4530-856d-17147decfb7a

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

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
theorem _root_.solution (p : ℕ) (k t : ℝ) : iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
  cases p with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']
end Formalism.FourierDecayAlt.P.LEx1
