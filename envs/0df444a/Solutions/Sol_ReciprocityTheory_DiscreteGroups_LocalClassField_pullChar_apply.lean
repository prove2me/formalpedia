-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.pullChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:09.811196+00:00
-- url     : https://prove2.me/submissions/b2d0d0f7-d114-4d21-ac6e-7d060cbc2d89

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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (ψ : A →+ QZ) (g : G) : (pullChar π hc ψ).1 (Additive.ofMul g) = ψ (π (Additive.ofMul g)) := rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
