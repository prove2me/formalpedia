-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.selfDualIndex_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:51.086004+00:00
-- url     : https://prove2.me/submissions/0ad2d3cd-1414-49ff-a6c9-37fd9d60a3e5

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordLat_fg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_intVec_le_coordLat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_spanIdx_eq_vecIdx
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordLat_selfDual
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_vec_selfDual_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open SemiDegIdx
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : SelfDualIndexStatement := by
  intro K _ _ r S L b hL hsd hb
  have key : |Algebra.norm ℚ (hGram S b).det| ≤ ((vecIdx (coordLat L b) : ℕ) : ℚ) ^ 2 :=
    vec_selfDual_bound (coordForm S b) _ (coordLat_fg hL.1 hb) (intVec_le_coordLat hb)
      (coordLat_selfDual hb hsd)
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key
end ReciprocityTheory.MultiplicativeHeights
