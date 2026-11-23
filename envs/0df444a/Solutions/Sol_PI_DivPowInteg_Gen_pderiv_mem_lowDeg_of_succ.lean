-- Prove2me | solution 1 for PI.DivPowInteg.Gen.pderiv_mem_lowDeg_of_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:30.393873+00:00
-- url     : https://prove2.me/submissions/18ca4741-13e2-473e-baf3-4e90d0ed0397

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
theorem _root_.solution {f : ι → σ} {t : ℕ} (i : ι) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f (t + 1)) : pderiv (f i) R ∈ lowDeg f t := by
  rw [mem_lowDeg] at h
  rw [R.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  rw [pderiv_monomial]
  by_cases h0 : m (f i) = 0
  · rw [h0]
    simp
  · rw [mem_lowDeg]
    intro m' hm'
    rw [Finset.mem_singleton.mp (support_monomial_subset hm')]
    have hlt := h m hm
    have key : ∑ i', (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f i') + 1 ≤ ∑ i', m (f i') := by
      classical
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have h1 : (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f i) + 1 = m (f i) := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      have h2 : ∑ x ∈ Finset.univ.erase i, (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f x) ≤
          ∑ x ∈ Finset.univ.erase i, m (f x) :=
        Finset.sum_le_sum (fun x _ => by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
      omega
    omega
end PI.DivPowInteg.Gen
