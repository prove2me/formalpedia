-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGenIndexMono_genIndex_nonneg_9f837cd075ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:31.424649+00:00
-- url     : https://prove2.me/submissions/b2e8b073-e136-4954-aba7-1e273c567ba1

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
theorem _root_.solution {G : Type*} [AddCommGroup G] (A B : AddSubgroup G) : 0 ≤ genIndex A B := by
  unfold genIndex
  positivity
end GroundTheory.Heights₂.Heights.KLinesGenIndexMono
