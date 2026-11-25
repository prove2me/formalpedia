-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutStairNonzero_proof_88e52650f95b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:14.886801+00:00
-- url     : https://prove2.me/submissions/6406406a-c62c-41c4-86a7-76792f60c798

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutStairNonzero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_flagIntegral_sub_C_mul_499e658ddad1

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
namespace RestCutStairNonzero
theorem _root_.solution (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestCutFlagKillsIdeal.Statement) : RestCutStairNonzero.Statement := by
  intro f N H hH hne hstair
  obtain ⟨b, hb⟩ := h₁ f N H hH
  have hmem : H - C b * restStair f N ∈ restPsumIdeal f N := hb
  have h0 := h₂ f N _ hmem
  rw [flagIntegral_sub_C_mul, hstair, mul_zero, sub_zero] at h0
  exact hne h0
end RestCutStairNonzero
end GroundTheory.Heights₂.Heights
