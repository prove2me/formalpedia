-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.so_emb_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:49.068934+00:00
-- url     : https://prove2.me/submissions/d4ff8575-2a7d-4f97-9eea-f5b996819da8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitOA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (v : (E →+* ℂ) → ℂ)
    (h : ∀ i, ∑ σ : E →+* ℂ, v σ * σ (RingOfIntegers.basis E i : E) = 0) : v = 0 := by
  classical
  have hM : (NumberField.basisMatrix E).mulVec v = 0 := by
    ext i
    rw [NumberField.basisMatrix_eq_embeddingsMatrixReindex]
    simp only [Matrix.mulVec, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply,
      NumberField.integralBasis_apply, Pi.zero_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm]
    rw [← h (NumberField.equivReindex E i)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [mul_comm]
    rfl
  have h2 := congrArg (fun u => (⅟(NumberField.basisMatrix E)).mulVec u) hM
  simp only [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.I2
