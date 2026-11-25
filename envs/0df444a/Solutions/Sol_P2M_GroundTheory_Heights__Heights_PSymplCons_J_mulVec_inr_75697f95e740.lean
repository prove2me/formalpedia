-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inr_75697f95e740
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:53.873977+00:00
-- url     : https://prove2.me/submissions/48fef638-2e81-49a7-8291-c55cb7e7e548

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplCons

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplCons
namespace GroundTheory.Heights₂.Heights.PSymplCons
theorem _root_.solution {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inr i) = v (Sum.inl i) := by
  simp [Matrix.J, fromBlocks_mulVec]
end GroundTheory.Heights₂.Heights.PSymplCons
