-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.nonempty_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:53.761225+00:00
-- url     : https://prove2.me/submissions/f3f4686d-517f-4c81-90fb-feed62c15a10

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function CategoryTheory
universe u
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] {M : Type u} [AddCommGroup M] [Module k M]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (H : AddSubgroup X)
    (φ : X →+ Y) (hφ : Surjective φ) (hk : ∀ x, φ x = 0 ↔ x ∈ H) : Nonempty (Y ≃+ X ⧸ H) := by
  have : φ.ker = H := by ext x; rw [AddMonoidHom.mem_ker, hk]
  subst this
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
