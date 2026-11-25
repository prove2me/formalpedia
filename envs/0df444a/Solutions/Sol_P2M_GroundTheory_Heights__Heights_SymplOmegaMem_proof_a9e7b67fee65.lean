-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplOmegaMem_proof_a9e7b67fee65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:11.094247+00:00
-- url     : https://prove2.me/submissions/7392fa7c-1cc2-4e48-aa40-13544248f5d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplOmegaMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplOmegaMem_mul_J_mul_transpose_apply_dee29cad7e8d

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
namespace GroundTheory.Heights₂.Heights
namespace SymplOmegaMem
theorem _root_.solution : SymplOmegaMem.Statement := by
  intro R _ l _ _ M
  rw [SymplecticGroup.mem_iff]
  constructor
  · intro h x y
    rw [← PSymplOmegaMem.mul_J_mul_transpose_apply, h]
  · intro h
    ext x y
    rw [PSymplOmegaMem.mul_J_mul_transpose_apply, h]
end SymplOmegaMem
end GroundTheory.Heights₂.Heights
