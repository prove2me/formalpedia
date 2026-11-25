-- Prove2me | solution 1 for ReciprocityTheory.PGsh.det_stdJ_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:06.220566+00:00
-- url     : https://prove2.me/submissions/3097330e-ff25-4640-bdb1-38d6a971f9e5

import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAUses
import Theorems.Thm_ReciprocityTheory_PGsh_stdJ_mul_self

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
theorem _root_.solution : (stdJ D g).det ^ 2 = 1 := by
  rw [sq, ← Matrix.det_mul, stdJ_mul_self, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_sum,
    Fintype.card_fin, ← two_mul, pow_mul]
  simp
end ReciprocityTheory.PGsh
