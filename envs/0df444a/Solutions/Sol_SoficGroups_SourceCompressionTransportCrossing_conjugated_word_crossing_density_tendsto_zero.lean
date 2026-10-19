-- Prove2me | solution 1 for SoficGroups.SourceCompressionTransportCrossing.conjugated_word_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/7eaedce9-c3c9-4cf9-85f4-ad2a9874e6db

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_comm
import Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_card_partitionWordCrossing_le_add_distance
import Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_tendsto_action_conjugate

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCompressionTransportCrossing
theorem _root_.solution
    {G : Type*} [Group G] (A : SoficGroups.SoficApproximation G)
    (u g : G)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hword : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action (u * g * u⁻¹))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)).card : ℝ) /
              (A.model n).size)
      atTop (nhds 0) := by
  have hdist : Tendsto
      (fun n => SoficGroups.normalizedHamming
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)
        ((A.model n).action (u * g * u⁻¹)))
      atTop (nhds 0) := by
    have heq :
        (fun n => SoficGroups.normalizedHamming
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)
          ((A.model n).action (u * g * u⁻¹))) =
        (fun n => SoficGroups.normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)) := by
      funext n
      exact SoficGroups.normalizedHamming_comm _ _
    rw [heq]
    exact tendsto_action_conjugate A u g
  have hupper : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action (u * g * u⁻¹))).card : ℝ) /
            (A.model n).size +
        SoficGroups.normalizedHamming
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)
          ((A.model n).action (u * g * u⁻¹)))
      atTop (nhds 0) := by
    simpa using hword.add hdist
  refine squeeze_zero (fun n => by positivity) ?_ hupper
  intro n
  have hnat := card_partitionWordCrossing_le_add_distance (Q n)
    ((A.model n).action u * (A.model n).action g *
      ((A.model n).action u)⁻¹)
    ((A.model n).action (u * g * u⁻¹))
  have hreal :
      ((SoficGroups.partitionWordCrossing (Q n)
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)).card : ℝ) ≤
      ((SoficGroups.partitionWordCrossing (Q n)
        ((A.model n).action (u * g * u⁻¹))).card : ℝ) +
      (SoficGroups.permutationDistance
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)
        ((A.model n).action (u * g * u⁻¹)) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((SoficGroups.partitionWordCrossing (Q n)
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)).card : ℝ) /
        (A.model n).size ≤
      (((SoficGroups.partitionWordCrossing (Q n)
        ((A.model n).action (u * g * u⁻¹))).card : ℝ) +
      (SoficGroups.permutationDistance
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)
        ((A.model n).action (u * g * u⁻¹)) : ℝ)) /
          (A.model n).size :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = ((SoficGroups.partitionWordCrossing (Q n)
        ((A.model n).action (u * g * u⁻¹))).card : ℝ) /
          (A.model n).size +
      SoficGroups.normalizedHamming
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)
        ((A.model n).action (u * g * u⁻¹)) := by
      simp [add_div, SoficGroups.normalizedHamming,
        SoficGroups.permutationDistance]
end SoficGroups.SourceCompressionTransportCrossing
