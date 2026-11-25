-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.theta_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:06:06.662455+00:00
-- url     : https://prove2.me/submissions/eb63fc96-69b5-4174-9d1b-66d1fd17c75a

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_mul_left_of_zero

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
include hc
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (g m : G) (hm : m ∈ N) (k : G) :
    c g (m * k) = c g m + ρ (g * m * g⁻¹) (c g k) := by
  have h1 := hc g m k
  have h2 := mul_left_of_zero hc h0 (g * m * g⁻¹) (Subgroup.Normal.conj_mem ‹_› m hm g) g k
  rw [inv_mul_cancel_right] at h2
  rw [h0 m hm, map_zero, h2] at h1
  linear_combination (norm := abel) h1
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
