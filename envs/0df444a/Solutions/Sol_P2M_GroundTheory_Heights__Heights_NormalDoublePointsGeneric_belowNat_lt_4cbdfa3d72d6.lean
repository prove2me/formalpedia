-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_belowNat_lt_4cbdfa3d72d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:11.880867+00:00
-- url     : https://prove2.me/submissions/fd30e9d0-f962-484f-bd0c-48d4dcee5b11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric

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
open MvPolynomial Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
namespace GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
theorem _root_.solution (d : ℕ) : belowNat d < (d : WithBot ℕ∞) := by
  cases d with
  | zero => exact WithBot.bot_lt_coe _
  | succ e =>
    show ((e : ℕ) : WithBot ℕ∞) < ((e + 1 : ℕ) : WithBot ℕ∞)
    exact_mod_cast Nat.lt_succ_self e
end GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
