-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:37.375858+00:00
-- url     : https://prove2.me/submissions/1df96f6a-766c-4880-86bb-6326976f6bf3

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
open _root_.Neutral.B1 Topology Function
open scoped commutatorElement
variable {F : Type*} [Field F] {L L' : IntermediateField F (AlgebraicClosure F)}
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
namespace ResCompat
theorem _root_.solution {hle : L ≤ L'} {σ' τ' : L' ≃ₐ[F] L'} {σ τ : L ≃ₐ[F] L}
    (h₁ : ResCompat hle σ' σ) (h₂ : ResCompat hle τ' τ) : ResCompat hle (σ' * τ') (σ * τ) := by
  intro x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h₂ x, h₁ (τ x)]
end ResCompat
end ReciprocityTheory.DiscreteGroups.GlobalClassField
