-- Prove2me | solution 1 for ReciprocityTheory.Cheb.half_le_normAtPlace_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:23.59713+00:00
-- url     : https://prove2.me/submissions/2071bd6f-2ac4-4fd0-871b-8da3b810316b

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_abs_normAtPlace_add_sub_le

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
variable {y k : mixedSpace E} {B a : ℝ}
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y)
    (w : InfinitePlace E) : normAtPlace w y / 2 ≤ normAtPlace w (y + k) := by
  have h := abs_normAtPlace_add_sub_le w y k
  rw [abs_le] at h
  linarith [hy w]
end ReciprocityTheory.Cheb
