-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesExtendBasis_span_single_eq_top_965f47190630
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:46.092666+00:00
-- url     : https://prove2.me/submissions/4e8c4de4-d2d8-4ba9-8cfb-f629be9cd116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesExtendBasis

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
open GroundTheory.Heights₂.Heights.KLinesExtendBasis
namespace GroundTheory.Heights₂.Heights.KLinesExtendBasis
theorem _root_.solution (K : Type) [Field K] (n : ℕ) :
    Submodule.span K (Set.range fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⊤ := by
  have h : (fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⇑(Pi.basisFun K (Fin n)) := by
    funext x
    simp
  rw [h]
  exact (Pi.basisFun K (Fin n)).span_eq
end GroundTheory.Heights₂.Heights.KLinesExtendBasis
