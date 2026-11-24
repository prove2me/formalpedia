-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvPolynomialReduction_proof_3ff9742bbded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:28.820875+00:00
-- url     : https://prove2.me/submissions/66dd7da7-f4e0-4d05-9701-af7614d03150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvPolynomialReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Coinv
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CoinvPolynomialReduction
theorem _root_.solution (h1 : CoinvMonomialReduction.Statement) :
    CoinvPolynomialReduction.Statement := by
  intro K _ _ f n H
  choose v hv hvI using fun d => h1 K f n d
  refine ⟨∑ d ∈ H.support, coeff d H • v d, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hv d)
  · have e1 : H - ∑ d ∈ H.support, coeff d H • v d =
        (∑ d ∈ H.support, monomial d (coeff d H)) - ∑ d ∈ H.support, coeff d H • v d := by
      rw [← H.as_sum]
    have e2 : (∑ d ∈ H.support, monomial d (coeff d H)) - ∑ d ∈ H.support, coeff d H • v d =
        ∑ d ∈ H.support, C (coeff d H) * (monomial d (1 : K) - v d) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_sub, C_mul_monomial, mul_one, smul_eq_C_mul]
    rw [e1, e2]
    exact Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hvI d)
end CoinvPolynomialReduction
end GroundTheory.Heights₂.Heights.RestTerms
