-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inl_c1577ead8cc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:53.152737+00:00
-- url     : https://prove2.me/submissions/9333568e-b7bc-41e4-b3f3-777a29fd1608

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
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inl i) = -v (Sum.inr i) := by
  simp [Matrix.J, fromBlocks_mulVec, neg_mulVec]
end GroundTheory.Heights₂.Heights.PSymplCons
