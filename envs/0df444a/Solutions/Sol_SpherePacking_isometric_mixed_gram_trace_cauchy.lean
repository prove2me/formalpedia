-- Prove2me | solution 1 for SpherePacking.isometric_mixed_gram_trace_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/492c09a4-6ab2-494a-8d29-6576a3058f46

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_finiteHilbertSchmidt_trace_cauchy
import Theorems.Thm_SpherePacking_isometric_projection_trace

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
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (C : Finset α) (f : α → F →ₗᵢ[ℝ] E) :
    ((C.card : ℝ) * (Module.finrank ℝ F : ℝ)) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        ∑ x ∈ C, ∑ y ∈ C,
          mixedHilbertSchmidtKernel b
            (fun z => (f z).toLinearMap)
            (fun z => (f z).toLinearMap) x y := by
  have h := finiteHilbertSchmidt_trace_cauchy b C
    (fun x => (f x).toLinearMap ∘ₗ (f x).adjoint)
  simp_rw [isometric_projection_trace] at h
  simpa [mixedHilbertSchmidtKernel] using h
end SpherePacking
