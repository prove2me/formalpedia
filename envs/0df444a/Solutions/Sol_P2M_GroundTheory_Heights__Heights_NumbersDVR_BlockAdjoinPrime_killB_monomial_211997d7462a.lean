-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_monomial_211997d7462a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:10.468231+00:00
-- url     : https://prove2.me/submissions/1095b491-64da-4af7-80af-f1d5cadbde37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
open Classical
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
theorem _root_.solution (B : Set K) (d : (Σ k, ι k) →₀ ℕ) (a : R) :
    killB (R := R) B (monomial d a) =
      if ∀ v ∈ d.support, v.1 ∉ B then monomial d a else 0 := by
  rw [killB, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    rw [if_neg (h v hv)]
  · push Not at h
    obtain ⟨v, hv, hB⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hv, mul_zero]
    rw [if_pos hB, zero_pow (Finsupp.mem_support_iff.mp hv)]
end GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
