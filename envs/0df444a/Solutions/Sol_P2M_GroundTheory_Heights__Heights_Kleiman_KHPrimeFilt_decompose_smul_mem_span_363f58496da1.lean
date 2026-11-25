-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_decompose_smul_mem_span_363f58496da1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:26.421067+00:00
-- url     : https://prove2.me/submissions/146a0f18-852b-4b49-892d-5574de308c11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} [DirectSum.Decomposition 𝓜]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
theorem _root_.solution (hgr : IsMGraded S ι 𝓜) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e)
    (r : MRingOver S ι) (c : K → ℤ) :
    (DirectSum.decompose 𝓜 (r • g) c : M) ∈ Submodule.span (MRingOver S ι) {g} := by
  classical
  rw [← r.support_sum_monomial_coeff]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  have hm : monomial d (coeff d r) • g ∈ 𝓜 (shift e (Finsupp.weight (blockWeight ι) d)) :=
    hgr.2 _ e _ g (isMultiHomog_of_isWeightedHomogeneous
      (isWeightedHomogeneous_monomial _ _ _ rfl)) hg
  by_cases h : shift e (Finsupp.weight (blockWeight ι) d) = c
  · subst h
    rw [DirectSum.decompose_of_mem_same _ hm]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
  · rw [DirectSum.decompose_of_mem_ne _ hm h]
    exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
