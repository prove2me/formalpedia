-- Prove2me | solution 1 for ReciprocityTheory.Cheb.normAtPlace_add_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:16.436093+00:00
-- url     : https://prove2.me/submissions/a8917e84-c29a-4b00-989a-4976a6d5bf6d

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_half_le_normAtPlace_add

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
theorem _root_.solution (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y)
    (w : InfinitePlace E) : 0 < normAtPlace w (y + k) := by
  have := half_le_normAtPlace_add hk ha hy w
  linarith [hy w]
end ReciprocityTheory.Cheb
