-- Prove2me | solution 1 for PI.DivPowInteg.Gen.pderiv_mem_lowDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:30.250871+00:00
-- url     : https://prove2.me/submissions/4c3d693b-cadf-4451-8c57-1eeb3208bf57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenVan
import Theorems.Thm_PI_DivPowInteg_Gen_mem_lowDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]
namespace PI.DivPowInteg.Gen
theorem _root_.solution {f : ι → σ} {t : ℕ} (k : σ) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f t) : pderiv k R ∈ lowDeg f t := by
  rw [mem_lowDeg] at h
  rw [R.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  rw [pderiv_monomial, mem_lowDeg]
  intro m' hm'
  rw [Finset.mem_singleton.mp (support_monomial_subset hm')]
  calc ∑ i, (m - Finsupp.single k 1 : σ →₀ ℕ) (f i) ≤ ∑ i, m (f i) :=
        Finset.sum_le_sum (fun i _ => by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
    _ < t := h m hm
end PI.DivPowInteg.Gen
