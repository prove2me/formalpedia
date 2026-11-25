-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integralIndex_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:10.676205+00:00
-- url     : https://prove2.me/submissions/beed037f-6597-490e-bc31-32c7a1ec0a60

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordLat_fg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_intVec_le_coordLat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_spanIdx_eq_vecIdx
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordLat_integral
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_vec_integral_bound


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
theorem _root_.solution : IntegralIndexStatement := by
  intro K _ _ r k S B b hB hb hint hdet
  have key : ((vecIdx (coordLat B b) : ℕ) : ℚ) ^ 2 ≤ |Algebra.norm ℚ (hGram S b).det| :=
    vec_integral_bound (coordForm S b) _ (coordLat_fg hB hb) (intVec_le_coordLat hb)
      (coordLat_integral hint) hdet
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key
end ReciprocityTheory.MultiplicativeHeights
