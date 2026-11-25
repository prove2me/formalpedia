-- Prove2me | solution 1 for ReciprocityTheory.PGsh.stdJ_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:52:06.963439+00:00
-- url     : https://prove2.me/submissions/fcd1e738-d0fd-4c9b-9f3c-1008ba3a0325

import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAUses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {D : Type} [CommRing D] {g : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution : stdJ D g * stdJ D g = -1 := by
  ext (i | i) (j | j) <;> simp [stdJ, Matrix.fromBlocks_multiply, Matrix.one_apply]
end ReciprocityTheory.PGsh
