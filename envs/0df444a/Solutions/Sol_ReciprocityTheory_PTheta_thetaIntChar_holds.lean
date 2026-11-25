-- Prove2me | solution 1 for ReciprocityTheory.PTheta.thetaIntChar_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:10.23482+00:00
-- url     : https://prove2.me/submissions/d313b128-c02c-4781-9881-fef49cc054b6

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int
import Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_add
import Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_intCast
import Theorems.Thm_ReciprocityTheory_PTheta_shiftVec_add_int
import Theorems.Thm_ReciprocityTheory_PTheta_shiftVec_dot_int

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
theorem _root_.solution : ThetaIntCharStatement := by
  intro ι _ a b n n' z τ
  unfold theta
  rw [← tsum_mul_left]
  conv_rhs => rw [← (Equiv.addRight n).tsum_eq]
  congr 1
  funext l
  simp only [Equiv.coe_addRight, thetaTerm, shiftVec_add_int, ofRealVec_add, ofRealVec_intCast]
  have hk : ∀ x : ℂ, eC (x + (((l + n) ⬝ᵥ n' : ℤ) : ℂ)) = eC x := fun x => by
    rw [eC_add, eC_int, mul_one]
  simp only [dotProduct_add, shiftVec_dot_int]
  conv_rhs => rw [← eC_add, ← hk]
  congr 1
  ring
end ReciprocityTheory.PTheta
