-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.det_flw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:23.579696+00:00
-- url     : https://prove2.me/submissions/3896e993-ed5b-4eb4-a38b-a861a86ce058

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramFlowTransform_gramF_flw

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
    (hA : IsUnit (gramF τ G f).det) : (gramF τ G (flw α e τ G f)).det =
      (gramF τ G f).det * (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  rw [gramF_flw hG e he α f, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateCol, replicateRow,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.mt, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
