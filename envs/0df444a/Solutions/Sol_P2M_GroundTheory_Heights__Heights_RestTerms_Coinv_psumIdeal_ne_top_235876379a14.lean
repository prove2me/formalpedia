-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_ne_top_235876379a14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:57.12868+00:00
-- url     : https://prove2.me/submissions/569e53a2-de58-4763-9d8a-1a7c3329a823

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_le_ker_3e0fba5eabdb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}
variable [CharZero K]
namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv
theorem _root_.solution : psumIdeal K f n ≠ ⊤ := by
  intro h
  have h1 : (1 : MvPolynomial (Fin f × Fin n) K) ∈ RingHom.ker constantCoeff :=
    psumIdeal_le_ker K (h ▸ Submodule.mem_top)
  simp at h1
end GroundTheory.Heights₂.Heights.RestTerms.Coinv
