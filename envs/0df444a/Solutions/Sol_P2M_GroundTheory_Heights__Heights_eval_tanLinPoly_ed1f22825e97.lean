-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_tanLinPoly_ed1f22825e97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:13.147946+00:00
-- url     : https://prove2.me/submissions/15e3af36-878b-4d41-beb5-fc0091a598fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (p w : Fin n → ℂ) : eval p (tanLinPoly p w) = 0 := by
  simp [tanLinPoly]
end GroundTheory.Heights₂.Heights
