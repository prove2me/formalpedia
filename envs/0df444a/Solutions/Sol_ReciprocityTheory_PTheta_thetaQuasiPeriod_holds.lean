-- Prove2me | solution 1 for ReciprocityTheory.PTheta.thetaQuasiPeriod_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:07:19.102863+00:00
-- url     : https://prove2.me/submissions/b39db768-dc64-443f-a50a-ec25c2410fa2

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int
import Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_intCast
import Theorems.Thm_ReciprocityTheory_PTheta_thetaRealTransl_holds
import Theorems.Thm_ReciprocityTheory_PTheta_thetaIntChar_holds

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
theorem _root_.solution : ThetaQuasiPeriodStatement := by
  intro ι _ a b z τ n n' hτ
  have h1 := thetaRealTransl_holds ι a b (fun i => (n i : ℝ)) (fun i => (n' i : ℝ)) z τ hτ
  simp only [ofRealVec_intCast] at h1
  rw [h1, thetaIntChar_holds, ← mul_assoc]
  congr 1
  unfold autFactor
  rw [← eC_add, ← eC_add]
  have hk : ofIntVec n ⬝ᵥ ofIntVec n' = ((n ⬝ᵥ n' : ℤ) : ℂ) := by
    simp [dotProduct, ofIntVec]
  have hk2 : ∀ x : ℂ, eC (x - ((n ⬝ᵥ n' : ℤ) : ℂ)) = eC x := fun x => by
    rw [sub_eq_add_neg, ← Int.cast_neg, eC_add, eC_int, mul_one]
  simp only [dotProduct_add, hk]
  rw [dotProduct_comm (ofIntVec n) (ofRealVec b)]
  conv_rhs => rw [← hk2]
  congr 1
  ring
end ReciprocityTheory.PTheta
