-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pcl_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:31.350401+00:00
-- url     : https://prove2.me/submissions/c2f7e1e8-8852-4e75-a21f-083fdf770b70

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (l : ℕ) (a : ZMod l) (s : ℝ) : 0 ≤ Pcl E l a s := by
  unfold Pcl
  refine tsum_nonneg (fun q => ?_)
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact le_rfl
end ReciprocityTheory.Cheb
