-- Prove2me | solution 1 for ReciprocityTheory.PTheta.thetaRealTransl_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:55:12.295019+00:00
-- url     : https://prove2.me/submissions/4066588b-11b2-4c75-b6a4-bdaa4627fe16

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm
import Theorems.Thm_ReciprocityTheory_PTheta_shiftVec_add_char
import Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta
theorem _root_.solution : ThetaRealTranslStatement := by
  intro ι _ a b u v z τ hτ
  unfold theta
  rw [← tsum_mul_left]
  congr 1
  funext l
  simp only [thetaTerm, shiftVec_add_char, ← eC_add, ofRealVec_add]
  congr 1
  simp only [mulVec_add, dotProduct_add, add_dotProduct,
    dot_mulVec_symm hτ (shiftVec a l) (ofRealVec u)]
  ring
end ReciprocityTheory.PTheta
