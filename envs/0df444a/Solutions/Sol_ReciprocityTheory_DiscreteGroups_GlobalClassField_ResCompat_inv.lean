-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:36.222595+00:00
-- url     : https://prove2.me/submissions/c25497fb-bf3d-4b37-9d09-e90fdfbe0491

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
theorem _root_.solution {hle : L ≤ L'} {τ' : L' ≃ₐ[F] L'} {τ : L ≃ₐ[F] L}
    (h : ResCompat hle τ' τ) : ResCompat hle τ'⁻¹ τ⁻¹ := by
  intro x
  apply τ'.injective
  rw [h (τ⁻¹ x)]
  show (τ' * τ'⁻¹) _ = IntermediateField.inclusion hle ((τ * τ⁻¹) x)
  rw [mul_inv_cancel, mul_inv_cancel]
  rfl
end ResCompat
end ReciprocityTheory.DiscreteGroups.GlobalClassField
