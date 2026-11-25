-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagStaircaseOrbit_proof_ee5852b2498a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:25.229547+00:00
-- url     : https://prove2.me/submissions/f6b1a94c-0d33-4771-9e16-276295472946

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagStaircaseOrbit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagStaircaseOrbit_bijective_of_injective_5dfb25d50c40

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagStaircaseOrbit
theorem _root_.solution : FlagStaircaseOrbit.Statement := by
  intro f N α β hα hβ iα iβ
  let A : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective α τ (hα τ) (iα τ))
  let B : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective β τ (hβ τ) (iβ τ))
  refine ⟨fun τ => (B τ).trans (A τ).symm, fun τ i => ?_⟩
  have h : A τ ((A τ).symm (B τ i)) = B τ i := Equiv.apply_symm_apply _ _
  have h' := congrArg Fin.val h
  exact h'
end FlagStaircaseOrbit
end GroundTheory.Heights₂.Heights.RestTerms
