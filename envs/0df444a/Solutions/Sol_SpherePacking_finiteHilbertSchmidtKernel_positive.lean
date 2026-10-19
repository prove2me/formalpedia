-- Prove2me | solution 1 for SpherePacking.finiteHilbertSchmidtKernel_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/9fe7a0b6-85f3-4ccb-b5a4-9e9cc3c95b42

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_positiveDefiniteKernel_of_features
import Theorems.Thm_SpherePacking_positiveDefiniteKernel_finset_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution
    {α ι F E : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ F)
    (A : α → F →ₗ[ℝ] E) :
    PositiveDefiniteKernel (finiteHilbertSchmidtKernel b A) := by
  classical
  unfold finiteHilbertSchmidtKernel
  apply positiveDefiniteKernel_finset_sum Finset.univ
    (fun i x y => ⟪A x (b i), A y (b i)⟫_ℝ)
  intro i hi
  exact positiveDefiniteKernel_of_features (fun x => A x (b i))
end SpherePacking
