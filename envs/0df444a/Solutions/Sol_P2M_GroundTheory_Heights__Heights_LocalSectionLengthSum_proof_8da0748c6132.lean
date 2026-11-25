-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_proof_8da0748c6132
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:05.082299+00:00
-- url     : https://prove2.me/submissions/0a587891-1372-4d5c-bdb1-099653833443

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPiQuotCokerFiniteLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLocalSectionLengthSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_quot_smul_top_eq_c98b42d6d7fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_pi_quot_smul_top_eq_cc6eec9c5118
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_quot_smul_eq_8287c0362885


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
open Module Submodule
open scoped Pointwise
namespace GroundTheory.Heights₂.Heights
namespace LocalSectionLengthSum
theorem _root_.solution (hPi : PiQuotCokerFiniteLength.Statement) :
    LocalSectionLengthSum.Statement := by
  intro B _ _ _ J f hJ hf hQ
  obtain ⟨hinj, hfin⟩ := hPi B J hJ hQ
  have hfinite := J.finite_minimalPrimes_of_isNoetherianRing B
  let _ : Fintype J.minimalPrimes := hfinite.fintype
  have hreg : Function.Injective fun x : ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) => f • x := by
    intro x y hxy
    funext P
    have : (P : Ideal B).IsPrime := P.2.1.1
    have h : f • x P = f • y P := congrFun hxy P
    rw [Algebra.smul_def, Algebra.smul_def] at h
    refine mul_left_cancel₀ ?_ h
    rw [Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf P P.2
  have e1 := Model.TorsionFreeQuotientLength.length_quot_smul_eq (quotToPiMinimalPrimes J) hinj
    hreg hfin
  rw [← LocalSectionLengthSum.length_quot_smul_top_eq J f, ← e1,
    LocalSectionLengthSum.length_pi_quot_smul_top_eq]
  simp_rw [LocalSectionLengthSum.length_quot_smul_top_eq]
  exact (Finset.sum_subtype (p := (· ∈ J.minimalPrimes)) hfinite.toFinset
    (fun P => hfinite.mem_toFinset)
    (fun P : Ideal B => Module.length B (B ⧸ (P ⊔ Ideal.span {f})))).symm
end LocalSectionLengthSum
end GroundTheory.Heights₂.Heights
