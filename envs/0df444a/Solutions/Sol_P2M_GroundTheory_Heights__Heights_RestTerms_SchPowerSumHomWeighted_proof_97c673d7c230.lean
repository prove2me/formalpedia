-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchPowerSumHomWeighted_proof_97c673d7c230
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:51.948836+00:00
-- url     : https://prove2.me/submissions/a31fc038-b98b-481a-bac7-822cff9cf2b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchPowerSumHomWeighted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_alt_cf5b2b7cf173
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf


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
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchPowerSumHomWeighted
theorem _root_.solution : SchPowerSumHomWeighted.Statement := by
  intro N d S hS
  rw [S.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun e he => ?_
  have hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = d :=
    hS (mem_support_iff.mp he)
  rw [powerSumHom, aeval_monomial, Finsupp.prod, algebraMap_eq]
  have hprod : (∏ i ∈ e.support, psum (Fin N) ℚ ((i : ℕ) + 1) ^ e i).IsHomogeneous
      (∑ i ∈ e.support, ((i : ℕ) + 1) * e i) :=
    IsHomogeneous.prod _ _ _ fun i _ => (psum_isHomogeneous_alt N ((i : ℕ) + 1)).pow (e i)
  have hsum : ∑ i ∈ e.support, ((i : ℕ) + 1) * e i = d := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hsum] at hprod
  exact hprod.C_mul _
end SchPowerSumHomWeighted
end GroundTheory.Heights₂.Heights.RestTerms
