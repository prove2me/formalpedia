-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isChowFormCycle_zero_one_4cd37bc8ca85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:49.894876+00:00
-- url     : https://prove2.me/submissions/77cf41ac-20e0-4a4f-b2b0-629def3a3fca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleSectionChow

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [Field F] {n k : ℕ} :
    IsChowFormCycle (0 : ProjCycle F n) k 1 :=
  ⟨1, one_ne_zero, fun _ => 1, by simp, by simp⟩
end GroundTheory.Heights₂.Heights
