-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.gramPos_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:48.741297+00:00
-- url     : https://prove2.me/submissions/f78a1e04-c514-4ca6-94dc-0a079b3bf43e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_gramPos_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_unipotentFrame_transpose_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_transpose_conj

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
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    X.gramPos (cpt X x0 z) τ = (n1 X z τ)ᵀ * Am X z τ * ((n1 X z τ)ᵀ)ᴴ := by
  rw [gramPos_cpt X x0 ho z τ, transpose_conj]
  unfold Am
  have hW := unipotentFrame_transpose_mul X z τ
  calc (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) - (Wm X z τ)ᵀ * (Wm X z τ).map (starRingEnd ℂ)
      = (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) -
          ((n1 X z τ)ᵀ * Zt X z τ) * ((n1 X z τ)ᵀ * Zt X z τ)ᴴ := by
        rw [hW, transpose_conj]
    _ = (n1 X z τ)ᵀ * (1 - Zt X z τ * (Zt X z τ)ᴴ) * (n1 X z τ).map (starRingEnd ℂ) := by
        rw [Matrix.conjTranspose_mul, transpose_conj]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
