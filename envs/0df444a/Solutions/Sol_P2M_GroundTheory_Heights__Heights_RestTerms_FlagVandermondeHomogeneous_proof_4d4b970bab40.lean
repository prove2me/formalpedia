-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeHomogeneous_proof_4d4b970bab40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:14:32.185081+00:00
-- url     : https://prove2.me/submissions/fcef547f-a2d4-4a8a-bcf7-1bbf4e2553ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagVandermondeHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_VandermondeOfHomogeneous_proof_eb784eab83eb


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
namespace FlagVandermondeHomogeneous
theorem _root_.solution : FlagVandermondeHomogeneous.Statement := by
  intro f N
  have hblock : ∀ τ : Fin f,
      (vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N))).IsHomogeneous
        (N * (N - 1) / 2) := fun τ =>
    VandermondeOfHomogeneous.proof _ _ N _ (fun i => isHomogeneous_X ℚ (τ, i))
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
    (fun τ => vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N)))
    (fun _ => N * (N - 1) / 2) (fun τ _ => hblock τ)
  simpa [blockVandermonde, topDegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] using h
end FlagVandermondeHomogeneous
end GroundTheory.Heights₂.Heights.RestTerms
