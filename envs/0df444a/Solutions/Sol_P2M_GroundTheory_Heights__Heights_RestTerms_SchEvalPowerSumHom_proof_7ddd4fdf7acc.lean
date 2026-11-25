-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchEvalPowerSumHom_proof_7ddd4fdf7acc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:01.522846+00:00
-- url     : https://prove2.me/submissions/525c085b-05b1-4624-98b9-d7b1be9bc7d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchEvalPowerSumHom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchEvalPowerSumHom_eq_single_of_dvd_8b89a10b6347

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
namespace SchEvalPowerSumHom
theorem _root_.solution (h1 : SchPowerSumAtRootsOfUnity.Statement) :
    SchEvalPowerSumHom.Statement := by
  intro N k hk1 hkN S hS
  have hzv : ∀ i : Fin N, aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1)) =
      if k ∣ (i : ℕ) + 1 then (k : ℂ) else 0 := fun i =>
    h1 N k ((i : ℕ) + 1) hk1 hkN (by omega)
  have hcomp : aeval (rootOfUnityPoint N k) (powerSumHom N S) =
      aeval (fun i : Fin N => aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1))) S := by
    rw [powerSumHom, ← AlgHom.comp_apply, comp_aeval]
  rw [hcomp]
  conv_lhs => rw [S.as_sum, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1)]
  · have hdvd : k ∣ ((⟨k - 1, by omega⟩ : Fin N) : ℕ) + 1 := by
      simp only [Nat.sub_add_cancel hk1, dvd_refl]
    rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, hzv, if_pos hdvd]
    simp [mul_comm]
  · intro e he hne
    rw [aeval_monomial]
    have hw := hS (MvPolynomial.mem_support_iff.mp he)
    obtain ⟨i, hi, hik⟩ : ∃ i ∈ e.support, ¬ k ∣ (i : ℕ) + 1 := by
      by_contra hcon
      push Not at hcon
      exact hne (SchEvalPowerSumHom.eq_single_of_dvd hk1 hkN e hw hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hzv, if_neg hik, zero_pow (Finsupp.mem_support_iff.mp hi)]
  · intro h
    rw [MvPolynomial.notMem_support_iff.mp h, monomial_zero, map_zero]
end SchEvalPowerSumHom
end GroundTheory.Heights₂.Heights.RestTerms
