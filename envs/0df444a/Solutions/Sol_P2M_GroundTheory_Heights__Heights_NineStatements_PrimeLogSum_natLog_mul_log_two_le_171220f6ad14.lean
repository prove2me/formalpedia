-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_natLog_mul_log_two_le_171220f6ad14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:44.492874+00:00
-- url     : https://prove2.me/submissions/94a29745-a3d5-4a07-b06d-f0c1300987b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PPrimeLogSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open Finset
open GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
namespace GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
theorem _root_.solution {N : ℕ} (hN : N ≠ 0) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h := Nat.pow_log_le_self 2 hN
  have h' : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at this
end GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
