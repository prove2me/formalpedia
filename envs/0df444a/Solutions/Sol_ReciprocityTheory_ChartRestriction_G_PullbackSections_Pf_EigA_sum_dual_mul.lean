-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.sum_dual_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:38.728138+00:00
-- url     : https://prove2.me/submissions/8928670b-5da0-4995-a858-78be960ae087

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) :
    ∑ i, TB.trDual b i * b i = 1 := by
  have key : ∀ y : E, Algebra.trace ℚ E ((∑ i, TB.trDual b i * b i - 1) * y) = 0 := by
    intro y
    rw [sub_mul, one_mul, map_sub, Algebra.trace_eq_matrix_trace (TB.trDual b) y, Matrix.trace,
      Finset.sum_mul, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, repr_trDual_lemma]
    congr 1
    ring
  have h0 : ∑ i, TB.trDual b i * b i - 1 = 0 := by
    apply (TB.trDual b).ext_elem
    intro j
    rw [repr_trDual_lemma, key, map_zero, Finsupp.zero_apply]
  exact sub_eq_zero.1 h0
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
