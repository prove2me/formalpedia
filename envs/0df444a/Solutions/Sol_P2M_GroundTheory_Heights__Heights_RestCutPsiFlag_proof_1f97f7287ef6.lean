-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutPsiFlag_proof_1f97f7287ef6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:18.373385+00:00
-- url     : https://prove2.me/submissions/52f2915e-4497-4e7b-933a-997eefa5f69c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutPsiFlag
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_coeff_psiPoly_9cd5be07914d


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
namespace RestCutPsiFlag
theorem _root_.solution : RestCutPsiFlag.Statement := by
  intro f N
  refine ⟨fun H => ?_, fun ψ P => ?_⟩
  · unfold realFlagIntegral RestTerms.flagIntegral
    push_cast [Rat.cast_sum, Rat.cast_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [coeff_map, eq_ratCast]
    ring
  · unfold realFlagIntegral RestTerms.flagIntegral
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [KRest.coeff_psiPoly]
    have h : coeff α P * ((coeff α (RestTerms.blockVandermonde f N) *
        α.prod (fun _ e => (e.factorial : ℚ)) : ℚ) : ℝ) =
        (coeff α (RestTerms.blockVandermonde f N) *
          α.prod (fun _ e => (e.factorial : ℚ))) • coeff α P := by
      rw [Rat.smul_def, mul_comm]
    rw [h, ψ.map_smul, smul_eq_mul]
    ring
end RestCutPsiFlag
end GroundTheory.Heights₂.Heights
