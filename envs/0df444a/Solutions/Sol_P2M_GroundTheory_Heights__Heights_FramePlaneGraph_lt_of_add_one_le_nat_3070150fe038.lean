-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FramePlaneGraph_lt_of_add_one_le_nat_3070150fe038
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:12.627942+00:00
-- url     : https://prove2.me/submissions/47691c0a-ffeb-4b53-8578-bf7f2253f0ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph

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
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace FramePlaneGraph
theorem _root_.solution {x : WithBot ℕ∞} {d : ℕ} (h : x + 1 ≤ (d : WithBot ℕ∞)) :
    x < d := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    have h' : y + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have hy : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
    have : y < d := (ENat.add_one_le_iff hy).mp h'
    exact_mod_cast this
end FramePlaneGraph
end GroundTheory.Heights₂.Heights
