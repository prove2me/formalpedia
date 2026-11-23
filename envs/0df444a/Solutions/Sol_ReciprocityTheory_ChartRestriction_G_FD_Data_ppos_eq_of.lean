-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:53.805399+00:00
-- url     : https://prove2.me/submissions/7d76ba41-a04e-4d1e-8dd7-82f3bcb14ec8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_sum_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (β : Fin X.p0 → ℂ)
    (horth : ∀ b : Fin X.p0, hermC τ.1 X.Gm (u - ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) :
    X.ppos x τ u = ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a) := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have hc : cf = Matrix.vecMul β A := by
    funext b
    have h := horth b
    rw [hC_sub_left, sub_eq_zero, hC_sum_left] at h
    simp only [cf, h, hC_smul_left, Matrix.vecMul, dotProduct, hAdef, gramPos, gram,
      Matrix.submatrix_apply, Matrix.of_apply]
  have hα : (fun a => ∑ b, cf b * A⁻¹ b a) = β := by
    have : Matrix.vecMul cf A⁻¹ = β := by
      rw [hc, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.vecMul_one]
    rw [← this]; rfl
  unfold ppos
  rw [← hα]
end ReciprocityTheory.ChartRestriction.G.FD.Data
