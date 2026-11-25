-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGenIndexMono_genIndex_of_le_e2c91bfa825c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:33.392956+00:00
-- url     : https://prove2.me/submissions/1dce829d-b237-4a73-9f8f-81c3e77cd34a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexMono

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
open GroundTheory.Heights₂.Heights.KLinesGenIndexMono
namespace GroundTheory.Heights₂.Heights.KLinesGenIndexMono
theorem _root_.solution {G : Type*} [AddCommGroup G] {A A' : AddSubgroup G} (h : A ≤ A') :
    genIndex A' A = (A.relIndex A' : ℝ) := by
  unfold genIndex
  rw [AddSubgroup.relIndex_eq_one.mpr h, Nat.cast_one, div_one]
end GroundTheory.Heights₂.Heights.KLinesGenIndexMono
