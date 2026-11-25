-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dual_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:59.595423+00:00
-- url     : https://prove2.me/submissions/30c0ef3d-c7ab-476b-857c-21ae959a57ec

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (x : E) :
    x = ∑ j, Algebra.trace ℚ E (x * b j) • TB.trDual b j := by
  conv_lhs => rw [← (TB.trDual b).sum_repr x]
  simp only [repr_trDual_lemma]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
