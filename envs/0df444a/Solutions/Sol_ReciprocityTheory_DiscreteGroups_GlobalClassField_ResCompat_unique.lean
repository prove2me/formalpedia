-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:27:38.026148+00:00
-- url     : https://prove2.me/submissions/c557c37c-8dcb-483c-b798-ed410e7bf066

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
theorem _root_.solution {hle : L ≤ L'} {τ' : L' ≃ₐ[F] L'} {τ₁ τ₂ : L ≃ₐ[F] L}
    (h₁ : ResCompat hle τ' τ₁) (h₂ : ResCompat hle τ' τ₂) : τ₁ = τ₂ := by
  ext x
  have := (h₁ x).symm.trans (h₂ x)
  exact congrArg Subtype.val ((IntermediateField.inclusion hle).toRingHom.injective this)
end ResCompat
end ReciprocityTheory.DiscreteGroups.GlobalClassField
