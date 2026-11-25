-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_of_succ_le_85c067b0ad94
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:04.626569+00:00
-- url     : https://prove2.me/submissions/6b6eb2b1-0ccd-4ff7-a425-59d02c115c95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {k : Type u} [Field k] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {d : WithBot ℕ∞} {D : ℕ} (h : d + 1 ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) :
    d ≤ (D : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    have h' : d + 1 ≤ (D : ℕ∞) + 1 := by exact_mod_cast h
    exact_mod_cast (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'
end GroundTheory.Heights₂.Heights.Kleiman
