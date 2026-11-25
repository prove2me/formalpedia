-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.mt_flw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:56.403445+00:00
-- url     : https://prove2.me/submissions/809d6907-92ee-4c9a-910b-1da9ebdfeb90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramFlowTransform_cv_flw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramFlowTransform_gramF_flw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramFlowTransform_mt_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramFlowTransform_det_flw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}
namespace ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
theorem _root_.solution (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) (h1 : 1 + (α + conj α) * GramDeterminantReal.mt τ G f e ≠ 0) :
    GramDeterminantReal.mt τ G (flw α e τ G f) e =
      GramDeterminantReal.mt τ G f e / (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  set s := α + conj α with hs
  set m := GramDeterminantReal.mt τ G f e with hm
  have hA' : IsUnit (gramF τ G (flw α e τ G f)).det := by
    rw [det_flw hG e he α f hA]
    exact hA.mul (isUnit_iff_ne_zero.mpr h1)
  have hyA : Matrix.vecMul (yv τ G f e) (gramF τ G f) = cv τ G f e := by
    simp only [GramDeterminantReal.yv, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  have hyB : Matrix.vecMul (yv τ G f e)
      (replicateCol Unit (fun a => s * conj (cv τ G f e a)) * replicateRow Unit (cv τ G f e)) =
      (s * m) • cv τ G f e := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, replicateCol, replicateRow,
      Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul]
    rw [hm, mt_y, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have key : Matrix.vecMul (yv τ G f e) (gramF τ G (flw α e τ G f)) =
      (1 + s * m) • cv τ G f e := by
    rw [gramF_flw hG e he α f, Matrix.vecMul_add, hyA, hyB, add_smul, one_smul]
  have hy : yv τ G (flw α e τ G f) e = (1 + s * m)⁻¹ • yv τ G f e := by
    have h2 : yv τ G f e = (1 + s * m) • yv τ G (flw α e τ G f) e := by
      conv_rhs => rw [GramDeterminantReal.yv, cv_flw hG e he α f, ← Matrix.smul_vecMul, ← key,
        Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA', Matrix.vecMul_one]
    rw [h2, smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [mt_y (flw α e τ G f) e, hy, cv_flw hG e he α f, div_eq_inv_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  congr 1
  exact (mt_y f e).symm
end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
