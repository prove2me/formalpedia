-- Prove2me | solution 1 for ReciprocityTheory.PTheta.thetaGL_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:40:49.102894+00:00
-- url     : https://prove2.me/submissions/389bd003-0b5f-4975-b144-a82e033e0766

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
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
theorem _root_.solution : ThetaGLStatement := by
  unfold ThetaGLStatement
  intro ι _ _ U a b z τ
  have h1 : ((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ)ᵀ * (U : Matrix ι ι ℤ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hVt : ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ =
      ((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) := by
    rw [← Matrix.transpose_map]
  have hWT : (((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ *
      ((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) = 1 := by
    ext i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] at h2 ⊢
    exact_mod_cast h2
  unfold theta
  conv_rhs => rw [← (transpEquiv U).tsum_eq]
  refine tsum_congr fun l => ?_
  have hs : shiftVec (((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℝ)))ᵀ *ᵥ a)
      ((U : Matrix ι ι ℤ)ᵀ *ᵥ l) =
      ((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ shiftVec a l := by
    rw [shiftVec_eq, shiftVec_eq, ← Matrix.transpose_map, ofIntVec_mulVec, ofRealVec_mulVec,
      Matrix.mulVec_add]
  have q : ∀ s : ι → ℂ, s ⬝ᵥ (((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) * τ *
      ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ) *ᵥ s) =
      (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s) ⬝ᵥ
        (τ *ᵥ (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s)) := by
    intro s
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hVt]
  have lin : ∀ s : ι → ℂ,
      s ⬝ᵥ ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ z + ofRealVec b) =
      (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s) ⬝ᵥ
        (z + ofRealVec (((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℝ)) *ᵥ b)) := by
    intro s
    have hl1 : s ⬝ᵥ ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ z) =
        (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s) ⬝ᵥ z := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hVt]
    have hl2 : (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s) ⬝ᵥ
        (((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec b) =
        s ⬝ᵥ ofRealVec b := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hWT,
        Matrix.one_mulVec]
    rw [ofRealVec_mulVec, dotProduct_add, dotProduct_add, hl1, hl2]
  simp only [transpEquiv, Equiv.coe_fn_mk]
  unfold thetaTerm
  rw [hs, q, lin]
end ReciprocityTheory.PTheta
