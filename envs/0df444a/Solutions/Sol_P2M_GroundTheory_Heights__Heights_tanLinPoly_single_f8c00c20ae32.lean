-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_tanLinPoly_single_f8c00c20ae32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:41:11.339962+00:00
-- url     : https://prove2.me/submissions/1699d327-3b86-48f6-99d0-c9cdfad14e84

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
theorem _root_.solution (p : Fin n → ℂ) (i : Fin n) :
    tanLinPoly p (Pi.single i 1) = X i - C (p i) := by
  classical
  simp only [tanLinPoly, Pi.single_apply]
  simp
end GroundTheory.Heights₂.Heights
