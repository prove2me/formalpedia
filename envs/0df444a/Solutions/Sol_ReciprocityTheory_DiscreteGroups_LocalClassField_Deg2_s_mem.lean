-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.s_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:14.399658+00:00
-- url     : https://prove2.me/submissions/8144c29b-c427-4a43-8015-1d465bc6d276

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)
variable {ρ}
variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)
include hrs hr
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution {n : G} (hn : n ∈ N) : s n ∈ N := by
  have h : s n = (r n)⁻¹ * n := by rw [eq_inv_mul_iff_mul_eq, hrs]
  rw [h]; exact N.mul_mem (N.inv_mem (hr n)) hn
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
