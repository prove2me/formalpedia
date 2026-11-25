-- Prove2me | solution 1 for P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomogIdeal_sup_span_844f7f9a9bdb87ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:40.773625+00:00
-- url     : https://prove2.me/submissions/2cf1a280-a3cf-40a8-bd5a-2d3709132df5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (F ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hF
  refine ⟨S ∪ {f}, fun g hg => ?_, (Ideal.span_union S {f}).symm⟩
  rcases hg with hg | hg
  · exact hS g hg
  · rw [Set.mem_singleton_iff] at hg
    exact ⟨c, hg ▸ hf⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
