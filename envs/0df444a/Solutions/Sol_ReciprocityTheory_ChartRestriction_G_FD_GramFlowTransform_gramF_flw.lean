-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.gramF_flw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:38.17373+00:00
-- url     : https://prove2.me/submissions/fe5841bd-52d0-4871-9c6b-37c888230e8f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_right


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
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    gramF τ G (flw α e τ G f) = gramF τ G f +
      replicateCol Unit (fun a => (α + conj α) * conj (cv τ G f e a)) *
        replicateRow Unit (cv τ G f e) := by
  ext a b
  have hc := GramDeterminantReal.hC_conj hG
  simp only [Matrix.add_apply, Matrix.mul_apply, replicateCol, replicateRow, Matrix.of_apply,
    Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.gramF, flw]
  rw [GramDeterminantReal.hC_add_left, GramDeterminantReal.hC_add_right, GramDeterminantReal.hC_add_right,
    GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_right,
    GramDeterminantReal.hermC_smul_right, he, hc e (f a)]
  all_goals try exact hG
  simp only [GramDeterminantReal.cv, map_mul]
  rw [← hc (f b) e]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
