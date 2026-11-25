-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutRealSyzygy_proof_4febf63f2dff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:35.788074+00:00
-- url     : https://prove2.me/submissions/b6ce498b-d877-4ea0-ba20-801c7385a482

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutRealSyzygy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutRealSyzygy_flagIntegral_zero_e83a39c3e0c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_eq_zero_of_forall_psi_85d62bcfb82e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_psiPoly_map_mul_4d01b38de564


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
namespace GroundTheory.Heights₂.Heights
namespace RestCutRealSyzygy
theorem _root_.solution (h₁ : RestTerms.RestTermWellDefined.Statement)
    (h₂ : RestCutPsiFlag.Statement) : RestCutRealSyzygy.Statement := by
  intro f N R hR m hm1 hmN τ G hG
  apply KRest.eq_zero_of_forall_psi
  intro ψ
  rw [(h₂ f N).2 ψ, KRest.psiPoly_map_mul]
  set Rψ : ℕ → Fin f → RestTerms.RootRing f N := fun l σ => KRest.psiPoly ψ (R l σ) with hRψ
  have hsyz : RestTerms.IsPowerSumDecomposition f N 0 Rψ := by
    have h0 := congrArg (KRest.psiPoly ψ) hR
    rw [map_zero, map_sum] at h0
    simp_rw [map_sum, KRest.psiPoly_map_mul] at h0
    exact h0.symm
  have hzero : RestTerms.IsPowerSumDecomposition f N 0 (fun _ _ => 0) := by
    simp [RestTerms.IsPowerSumDecomposition]
  have h := h₁ f N 0 Rψ (fun _ _ => 0) hsyz hzero m hm1 hmN τ G hG
  simp only [RestTerms.restTerm, mul_zero, RestCutRealSyzygy.flagIntegral_zero] at h
  have hm : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  exact (mul_eq_zero.mp h).resolve_left hm
end RestCutRealSyzygy
end GroundTheory.Heights₂.Heights
