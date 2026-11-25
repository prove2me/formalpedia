-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_equiv_zero_fbc06038a4c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:53:54.686671+00:00
-- url     : https://prove2.me/submissions/e9bafcb3-eefb-4837-9845-883dac5fc8b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {A B : Type} (E : A ≃ B) (d : A → ℕ) :
    Function.extend E d 0 = d ∘ E.symm := by
  funext b
  obtain ⟨a, rfl⟩ := E.surjective b
  simp [E.injective.extend_apply]
end GroundTheory.Heights₂.Heights.FieldNumbers
