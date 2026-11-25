-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.stepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:41.46862+00:00
-- url     : https://prove2.me/submissions/d2a6a996-750c-4cda-9339-c709b16066f8

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
theorem _root_.solution [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (h0' : ∀ n ∈ N, ∀ g, c g n = 0) (n : G) (hn : n ∈ N)
    (g h : G) : c g (h * n) = c g h ∧ c (g * n) h = c g h ∧ ρ n (c g h) = c g h := by
  have hR : ∀ g h n, n ∈ N → c g (h * n) = c g h := fun g h n hn => by
    have h1 := hc g h n
    rw [h0' n hn, h0' n hn, map_zero] at h1
    linear_combination (norm := abel) h1
  have hL : ∀ g h n, n ∈ N → c g (n * h) = c g h := fun g h n hn => by
    have : n * h = h * (h⁻¹ * n * h) := by group
    rw [this, hR _ _ _ (Subgroup.Normal.conj_mem' ‹_› n hn h)]
  have hM : ∀ g h n, n ∈ N → c (g * n) h = c g h := fun g h n hn => by
    have h1 := hc g n h
    rw [h0 n hn, h0' n hn, map_zero, hL _ _ _ hn] at h1
    linear_combination (norm := abel) - h1
  refine ⟨hR g h n hn, hM g h n hn, ?_⟩
  rw [← mul_left_of_zero hc h0 n hn]
  have : n * g = g * (g⁻¹ * n * g) := by group
  rw [this, hM _ _ _ (Subgroup.Normal.conj_mem' ‹_› n hn g)]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
