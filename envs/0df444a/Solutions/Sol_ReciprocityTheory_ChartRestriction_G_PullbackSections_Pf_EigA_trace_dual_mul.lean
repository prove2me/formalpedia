-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.trace_dual_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:46.437419+00:00
-- url     : https://prove2.me/submissions/bd159033-7444-4763-8f2e-7ecd6cd50795

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBIdemDen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {E : Type} [Field E] [NumberField E]
private theorem repr_trDual_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E)
    (x : E) (j : ι) : (TB.trDual b).repr x j = Algebra.trace ℚ E (x * b j) := by
  have h := LinearMap.BilinForm.dualBasis_repr_apply
    (traceForm_nondegenerate ℚ E) b x j
  rw [Algebra.traceForm_apply] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (i k : ι) :
    Algebra.trace ℚ E (TB.trDual b i * b k) = if k = i then 1 else 0 := by
  rw [← repr_trDual_lemma, Module.Basis.repr_self]
  by_cases hki : k = i
  · subst hki; simp
  · rw [if_neg hki, Finsupp.single_apply, if_neg (Ne.symm hki)]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
