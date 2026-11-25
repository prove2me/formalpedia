-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_smul_of_isHomogeneous_28aad74d1df1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:51.700313+00:00
-- url     : https://prove2.me/submissions/66faaed3-1bb5-4a7e-a51b-9a4619d8cc5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel

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
open GroundTheory.Heights₂.Heights.ChartKernel
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution {F σ S : Type*} [Field F] [CommRing S] [Algebra F S]
    {φ : MvPolynomial σ F} {d : ℕ} (hφ : φ.IsHomogeneous d) (a : S) (x : σ → S) :
    aeval (a • x) φ = a ^ d * aeval x φ := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : ∑ i ∈ s.support, s i = d := by
    rw [← hφ (mem_support_iff.mp hs)]
    simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs']
  ring
end GroundTheory.Heights₂.Heights.ChartKernel
