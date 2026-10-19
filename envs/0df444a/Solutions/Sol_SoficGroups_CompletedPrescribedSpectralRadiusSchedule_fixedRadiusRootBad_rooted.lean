-- Prove2me | solution 1 for SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_rooted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/627cc1e2-a39b-4866-ab60-53872c80d7a3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_mem_generator_pow_of_chosen_word_length
import Theorems.Thm_SoficGroups_CompletedPrescribedSpectralRadiusSchedule_mem_generator_pow_of_chosen_word_length

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedPrescribedSpectralRadiusSchedule
open Filter Topology
open scoped Pointwise
namespace SoficGroups.CompletedPrescribedSpectralRadiusSchedule
theorem _root_.solution
    {G V : Type*} [Group G] [DecidableEq G]
    [Fintype V] [DecidableEq V]
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ a : G,
      ((w a).map fun i : ↥S => (i : G)).prod = a)
    (φ : G → Equiv.Perm V) (r : ℕ)
    (a g : G)
    (hr : (w a).length + (w g).length +
      (w (a * g)).length ≤ r)
    (x : V) (hx : x ∉ fixedRadiusRootBad φ S r) :
    φ (a * g) x = (φ a * φ g) x := by
  have ha : a ∈ S ^ r :=
    mem_generator_pow_of_chosen_word_length S hone w hw (by omega)
  have hg : g ∈ S ^ r :=
    mem_generator_pow_of_chosen_word_length S hone w hw (by omega)
  by_contra hfailure
  apply hx
  unfold fixedRadiusRootBad
  apply Finset.mem_biUnion.mpr
  refine ⟨(a, g), Finset.mem_product.mpr ⟨ha, hg⟩, ?_⟩
  unfold multiplicationBad
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfailure⟩
end SoficGroups.CompletedPrescribedSpectralRadiusSchedule
