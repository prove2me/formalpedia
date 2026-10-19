-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_rooted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/6e9859d6-cad4-4507-acf0-3f5f225b95db

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenFiniteMultiplicationBad_rooted
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_mem_generator_pow_of_chosen_word_length

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ g, ((w g).map fun i : ↥S => (i : G)).prod = g)
    (n r : ℕ) (a g : G)
    (hword : (w a).length + (w g).length +
      (w (a * g)).length ≤ r)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenCayleyRadiusBad A S w n r) :
    chosenWordEvaluation A (fun i : ↥S => (i : G)) w n (a * g) x =
      (chosenWordEvaluation A (fun i : ↥S => (i : G)) w n a *
        chosenWordEvaluation A (fun i : ↥S => (i : G)) w n g) x := by
  have ha : (w a).length ≤ r := by omega
  have hg : (w g).length ≤ r := by omega
  have ha' : a ∈ S ^ r :=
    mem_generator_pow_of_chosen_word_length S hone w hw ha
  have hg' : g ∈ S ^ r :=
    mem_generator_pow_of_chosen_word_length S hone w hw hg
  apply chosenFiniteMultiplicationBad_rooted
    A (fun i : ↥S => (i : G)) w (S ^ r) n ha' hg'
  intro hbad
  exact hx (Finset.mem_union_right _ hbad)
end SoficGroups.KunActualSoficRootRadius
