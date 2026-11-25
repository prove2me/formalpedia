-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.pullChar_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:40.048035+00:00
-- url     : https://prove2.me/submissions/375489f6-a5d5-43ed-b94d-b8ccba70dd6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecAbA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Function
noncomputable section
variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))
variable {π}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hπ : Surjective π) : Injective (pullChar π hc) := by
  intro ψ ψ' h
  ext a
  obtain ⟨g, rfl⟩ := hπ a
  exact DFunLike.congr_fun (congrArg Subtype.val h) g
end ReciprocityTheory.DiscreteGroups.LocalClassField
