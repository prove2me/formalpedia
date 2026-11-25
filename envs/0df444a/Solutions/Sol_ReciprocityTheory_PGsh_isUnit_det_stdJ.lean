-- Prove2me | solution 1 for ReciprocityTheory.PGsh.isUnit_det_stdJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:09.151972+00:00
-- url     : https://prove2.me/submissions/132e80d6-f9e9-40be-a96a-46eebcee0d14

import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAUses
import Theorems.Thm_ReciprocityTheory_PGsh_det_stdJ_sq

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
theorem _root_.solution : IsUnit (stdJ D g).det := by
  exact isUnit_iff_exists_inv.2 ⟨(stdJ D g).det, by rw [← sq, det_stdJ_sq]⟩
end ReciprocityTheory.PGsh
