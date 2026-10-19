-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.fixed_generated_word_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/34eb005c-cb5d-4dd9-b3c9-aa63b8c5516a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_action_list_prod_tendsto
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_generator_crossing_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_list_generator_crossing_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_action_list_prod_tendsto
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_exists_word_of_symmetric_generators
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_crossing_density_tendsto_zero_of_normalizedHamming

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    {G H : Type*} [Group G] [Group H]
    (A : SoficGroups.SoficApproximation G)
    (φ : H →* G) (S : Finset H)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set H) = ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S => (A.model n).action (φ (i : H))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0))
    (g : H) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action (φ g))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
  classical
  obtain ⟨l, hl⟩ :=
    exists_word_of_symmetric_generators S hsymmetric hgenerates g
  have hgenerator (i : ↥S) : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action (φ (i : H)))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
    simpa only [Fintype.card_fin] using
      generator_crossing_density_tendsto_zero
        (V := fun n => Fin (A.model n).size)
        Q (fun n (j : ↥S) => (A.model n).action (φ (j : H)))
        (by simpa only [Fintype.card_fin] using hboundary) i
  have hlist : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((l.map fun i : ↥S =>
            (A.model n).action (φ (i : H))).prod)).card : ℝ) /
              (A.model n).size)
      atTop (nhds 0) := by
    simpa only [Fintype.card_fin] using
      list_generator_crossing_density_tendsto_zero
        (V := fun n => Fin (A.model n).size)
        Q (fun n (i : ↥S) => (A.model n).action (φ (i : H)))
        (fun i => by
          simpa only [Fintype.card_fin] using hgenerator i)
        l
  have hprod :
      ((l.map fun i : ↥S => φ (i : H)).prod) = φ g := by
    calc
      ((l.map fun i : ↥S => φ (i : H)).prod) =
          φ ((l.map fun i : ↥S => (i : H)).prod) := by
        simpa [List.map_map, Function.comp_def] using
          (map_list_prod φ (l.map fun i : ↥S => (i : H))).symm
      _ = φ g := by rw [hl]
  have hdist : Tendsto
      (fun n => SoficGroups.normalizedHamming
        ((A.model n).action (φ g))
        ((l.map fun i : ↥S =>
          (A.model n).action (φ (i : H))).prod))
      atTop (nhds 0) := by
    have h := action_list_prod_tendsto A
      (l.map fun i : ↥S => φ (i : H))
    rw [hprod] at h
    simpa [List.map_map, Function.comp_def] using h
  simpa only [Fintype.card_fin] using
    crossing_density_tendsto_zero_of_normalizedHamming
      (V := fun n => Fin (A.model n).size)
      Q (fun n => (A.model n).action (φ g))
      (fun n =>
        (l.map fun i : ↥S => (A.model n).action (φ (i : H))).prod)
      (by simpa only [Fintype.card_fin] using hlist)
      hdist
end SoficGroups.SourceGeneratedWordCrossing
