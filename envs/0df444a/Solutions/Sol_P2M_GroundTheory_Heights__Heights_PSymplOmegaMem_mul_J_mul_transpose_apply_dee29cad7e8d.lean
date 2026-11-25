-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplOmegaMem_mul_J_mul_transpose_apply_dee29cad7e8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:09.410221+00:00
-- url     : https://prove2.me/submissions/6e709fac-0d2d-45e2-b96f-cf9b603b2cf5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplOmegaMem

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
open GroundTheory.Heights₂.Heights.PSymplOmegaMem
namespace GroundTheory.Heights₂.Heights.PSymplOmegaMem
theorem _root_.solution {R : Type*} [CommRing R] {l : Type*} [Fintype l]
    [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) R) (x y : l ⊕ l) :
    (M * J l R * Mᵀ) x y = symplOmega (M x) (M y) := by
  rw [symplOmega, dotProduct_mulVec, Matrix.mul_apply]
  rfl
end GroundTheory.Heights₂.Heights.PSymplOmegaMem
