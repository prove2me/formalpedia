-- Prove2me | solution 1 for SoficGroups.CompletedChosenWordLocalRoot.chosenWordEvaluation_tendsto_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/c3281e86-e00d-4d15-a729-4ff96aeff1d2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_comm
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_list_permutation_hamming_tendsto
import Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_approximate_action_list_prod_tendsto

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators
namespace SoficGroups.CompletedChosenWordLocalRoot
theorem _root_.solution
    {G ι : Type*} [Group G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (p : ∀ n, G → Equiv.Perm (V n))
    (hone : ∀ n, p n 1 = 1)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (p n (a * g)) (p n a * p n g))
        atTop (nhds 0))
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g : G, ((w g).map s).prod = g)
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hletter : ∀ i : ι,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (σ n i) (p n (s i)))
        atTop (nhds 0))
    (g : G) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        (chosenWordEvaluation (σ n) w g) (p n g))
      atTop (nhds 0) := by
  have hσ : Tendsto
      (fun n => SoficGroups.normalizedHamming
        (chosenWordEvaluation (σ n) w g)
        (((w g).map fun i => p n (s i)).prod))
      atTop (nhds 0) := by
    exact list_permutation_hamming_tendsto V
      σ (fun n i => p n (s i)) hletter (w g)
  have hp : Tendsto
      (fun n => SoficGroups.normalizedHamming
        (p n g) (((w g).map fun i => p n (s i)).prod))
      atTop (nhds 0) := by
    have h := approximate_action_list_prod_tendsto
      V p hone hmul ((w g).map s)
    simpa [List.map_map, Function.comp_def, hw g] using h
  have hp' : Tendsto
      (fun n => SoficGroups.normalizedHamming
        (((w g).map fun i => p n (s i)).prod) (p n g))
      atTop (nhds 0) := by
    have heq :
        (fun n => SoficGroups.normalizedHamming
          (((w g).map fun i => p n (s i)).prod) (p n g)) =
        (fun n => SoficGroups.normalizedHamming
          (p n g) (((w g).map fun i => p n (s i)).prod)) := by
      funext n
      exact SoficGroups.normalizedHamming_comm _ _
    rw [heq]
    exact hp
  have hupper : Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (chosenWordEvaluation (σ n) w g)
          (((w g).map fun i => p n (s i)).prod) +
        SoficGroups.normalizedHamming
          (((w g).map fun i => p n (s i)).prod) (p n g))
      atTop (nhds 0) := by
    simpa using hσ.add hp'
  exact squeeze_zero
    (fun n => SoficGroups.normalizedHamming_nonneg _ _)
    (fun n => SoficGroups.normalizedHamming_triangle _ _ _)
    hupper
end SoficGroups.CompletedChosenWordLocalRoot
