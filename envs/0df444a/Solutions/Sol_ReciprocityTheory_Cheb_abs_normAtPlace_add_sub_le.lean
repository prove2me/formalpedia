-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_normAtPlace_add_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:06.811853+00:00
-- url     : https://prove2.me/submissions/9732699d-c3e9-4366-af35-326580dc5b2b

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_P2M_ReciprocityTheory_Cheb_normAtPlace_le_norm__43bb5f9414e5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (w : InfinitePlace E) (y k : mixedSpace E) :
    |normAtPlace w (y + k) - normAtPlace w y| ≤ ‖k‖ := by
  have h1 := normAtPlace_add_le w y k
  have h2 := normAtPlace_add_le w (y + k) (-k)
  rw [add_neg_cancel_right, normAtPlace_neg] at h2
  have h3 := normAtPlace_le_norm' w k
  rw [abs_le]; constructor <;> linarith
end ReciprocityTheory.Cheb
