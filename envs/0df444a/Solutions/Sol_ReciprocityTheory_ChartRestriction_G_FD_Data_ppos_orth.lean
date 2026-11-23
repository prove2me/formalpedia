-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:43.705539+00:00
-- url     : https://prove2.me/submissions/70904bdc-164f-400d-a72b-5dec8c948f5e

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
    (b : Fin X.p0) : hermC τ.1 X.Gm (u - X.ppos x τ u) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have key : Matrix.vecMul (Matrix.vecMul cf A⁻¹) A = cf := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hA), Matrix.vecMul_one]
  have h2 := congrFun key b
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [hC_sub_left, sub_eq_zero]
  unfold ppos
  rw [hC_sum_left]
  simp only [hC_smul_left]
  rw [show hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) = cf b from rfl, ← h2]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.Data
