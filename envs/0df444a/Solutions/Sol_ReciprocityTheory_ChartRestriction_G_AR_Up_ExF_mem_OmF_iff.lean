-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mem_OmF_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:36.608078+00:00
-- url     : https://prove2.me/submissions/adb17031-ccc1-4f2c-a46e-c0cad82575c4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_ne_of_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_nM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mat_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_unipotentFrame_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_gramPos_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_dom_of_gramPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) : z ∈ OmF X x0 ↔ ∀ τ, (Am X z τ).PosDef := by
  have hdx : ∀ τ, (mat (cpt X x0 z) τ).det ≠ 0 := by
    intro τ
    rw [mat_cpt, Matrix.det_mul, det_nM, mul_one]
    exact det_ne_of_orth X ho τ
  have hB : ∀ τ, IsUnit ((n1 X z τ)ᵀ).det := by
    intro τ
    rw [Matrix.det_transpose, det_unipotentFrame_eq_one]
    exact isUnit_one
  constructor
  · intro hz τ
    have hP := Data.gramPos_posDef (X := X) (show cpt X x0 z ∈ X.dom from hz) τ
    rw [gramPos_eq X x0 ho z τ] at hP
    have hC : ((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ = 1 := Matrix.nonsing_inv_mul _ (hB τ)
    have hA : Am X z τ = ((n1 X z τ)ᵀ)⁻¹ * ((n1 X z τ)ᵀ * Am X z τ * ((n1 X z τ)ᵀ)ᴴ) *
        (((n1 X z τ)ᵀ)⁻¹)ᴴ := by
      calc Am X z τ = (((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ) * Am X z τ *
            (((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ)ᴴ := by rw [hC]; simp
        _ = _ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [hA]
    refine hP.mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h3 := congrArg (fun u => Matrix.vecMul u (n1 X z τ)ᵀ) hvw
    simpa [Matrix.vecMul_vecMul, hC] using h3
  · intro hA
    show cpt X x0 z ∈ X.dom
    refine mem_dom_of_gramPos (X := X) (fun τ => ⟨hdx τ, ?_⟩)
    rw [gramPos_eq X x0 ho z τ]
    refine (hA τ).mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h3 := congrArg (fun u => Matrix.vecMul u ((n1 X z τ)ᵀ)⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hB τ)] using h3
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
