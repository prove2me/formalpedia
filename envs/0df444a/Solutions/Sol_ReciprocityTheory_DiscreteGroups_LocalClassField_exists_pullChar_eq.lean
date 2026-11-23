-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_pullChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:10.918931+00:00
-- url     : https://prove2.me/submissions/c81cadb2-6546-4ff1-8848-b25e80dd01ad

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
theorem _root_.solution (hπ : Surjective π) (χ : charGrp G)
    (h : ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) : ∃ ψ, pullChar π hc ψ = χ := by
  refine ⟨π.liftOfSurjective hπ ⟨χ.1, fun g hg => h (Additive.toMul g) hg⟩, Subtype.ext ?_⟩
  exact AddMonoidHom.liftOfRightInverse_comp _ _ _ _
end ReciprocityTheory.DiscreteGroups.LocalClassField
