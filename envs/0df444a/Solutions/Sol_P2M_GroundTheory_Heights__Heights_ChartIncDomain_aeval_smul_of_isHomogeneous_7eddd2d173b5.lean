-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_smul_of_isHomogeneous_7eddd2d173b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:45.418878+00:00
-- url     : https://prove2.me/submissions/044c1723-19cf-4f6e-880c-d48f1d5fc8ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncDomain
namespace GroundTheory.Heights₂.Heights.ChartIncDomain
theorem _root_.solution {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : S) (x : σ → S) :
    aeval (c • x) p = c ^ d * aeval x p := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : ∑ i ∈ s.support, s i = d := by
    have := hp (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs']
  ring
end GroundTheory.Heights₂.Heights.ChartIncDomain
