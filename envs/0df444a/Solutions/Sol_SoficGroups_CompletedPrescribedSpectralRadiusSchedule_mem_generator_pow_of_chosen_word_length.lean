-- Prove2me | solution 1 for SoficGroups.CompletedPrescribedSpectralRadiusSchedule.mem_generator_pow_of_chosen_word_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/e862cded-4ad4-40a3-b366-7ab14b5c8b49

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedPrescribedSpectralRadiusSchedule
open Filter Topology
open scoped Pointwise
namespace SoficGroups.CompletedPrescribedSpectralRadiusSchedule
theorem _root_.solution
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ a : G,
      ((w a).map fun i : ↥S => (i : G)).prod = a)
    {a : G} {r : ℕ} (ha : (w a).length ≤ r) :
    a ∈ S ^ r := by
  have hprod : ∀ l : List ↥S,
      ((l.map fun i : ↥S => (i : G)).prod) ∈ S ^ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
        simpa [pow_succ', List.prod_cons] using
          (Finset.mul_mem_mul i.property ih)
  apply Finset.pow_subset_pow_right hone ha
  simpa only [hw a] using hprod (w a)
end SoficGroups.CompletedPrescribedSpectralRadiusSchedule
