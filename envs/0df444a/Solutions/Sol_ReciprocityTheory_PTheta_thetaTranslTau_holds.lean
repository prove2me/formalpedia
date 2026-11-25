-- Prove2me | solution 1 for ReciprocityTheory.PTheta.thetaTranslTau_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:04:12.592874+00:00
-- url     : https://prove2.me/submissions/e9510e5d-5a21-4413-8866-947308e16806

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Theorems.Thm_ReciprocityTheory_PTheta_quad_diag_int
import Theorems.Thm_ReciprocityTheory_PTheta_eC_eq_of_int
import Theorems.Thm_ReciprocityTheory_PTheta_shiftVec_eq
import Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_mulVec
import Theorems.Thm_ReciprocityTheory_PTheta_ofIntVec_mulVec

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
theorem _root_.solution : ThetaTranslTauStatement := by
  unfold ThetaTranslTauStatement
  intro ι _ a b z τ B hB
  have hadd : ∀ x y : ℂ, eC (x + y) = eC x * eC y := fun x y => by
    simp only [eC, mul_add, Complex.exp_add]
  have hb' : ofRealVec (b + B.map (fun x : ℤ => (x : ℝ)) *ᵥ a + fun i => ((B i i : ℤ) : ℝ) / 2) =
      ofRealVec b + B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec a + fun i => ((B i i : ℤ) : ℂ) / 2 := by
    rw [← ofRealVec_mulVec]
    funext i
    simp [ofRealVec]
  have hBc : (B.map (fun x : ℤ => (x : ℂ)))ᵀ = B.map (fun x : ℤ => (x : ℂ)) := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.map_apply, hB.apply i j]
  unfold theta
  rw [← tsum_mul_left]
  refine tsum_congr fun l => ?_
  obtain ⟨k, hk⟩ := quad_diag_int B hB l
  have hkC : ofIntVec l ⬝ᵥ (B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofIntVec l) =
      ofIntVec l ⬝ᵥ (fun i => ((B i i : ℤ) : ℂ)) + 2 * (k : ℂ) := by
    have e1 : ofIntVec l ⬝ᵥ ofIntVec (B *ᵥ l) = ((l ⬝ᵥ (B *ᵥ l) : ℤ) : ℂ) := by
      simp [dotProduct, ofIntVec]
    have e2 : ofIntVec l ⬝ᵥ (fun i => ((B i i : ℤ) : ℂ)) = ((l ⬝ᵥ (fun i => B i i) : ℤ) : ℂ) := by
      simp [dotProduct, ofIntVec]
    rw [← ofIntVec_mulVec, e1, e2, hk]
    first
      | (push_cast; done)
      | (push_cast; ring)
  have hsA : ofRealVec a ⬝ᵥ (B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofIntVec l) =
      ofIntVec l ⬝ᵥ (B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec a) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBc, dotProduct_comm]
  have hhL : ofIntVec l ⬝ᵥ (fun i => ((B i i : ℤ) : ℂ) / 2) =
      (ofIntVec l ⬝ᵥ fun i => ((B i i : ℤ) : ℂ)) / 2 := by
    simp only [dotProduct, Finset.sum_div, mul_div_assoc]
  unfold thetaTerm
  rw [← hadd]
  apply eC_eq_of_int _ _ k
  rw [hb', shiftVec_eq]
  simp only [Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  linear_combination (1 / 2 : ℂ) * hkC + (1 / 2 : ℂ) * hsA - hhL
end ReciprocityTheory.PTheta
