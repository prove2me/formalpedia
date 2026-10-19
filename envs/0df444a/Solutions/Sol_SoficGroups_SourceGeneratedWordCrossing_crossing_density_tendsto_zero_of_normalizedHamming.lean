-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.crossing_density_tendsto_zero_of_normalizedHamming
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/56c2179f-8e7e-4798-86fc-ab45e29c2896

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_card_partitionWordCrossing_le_add_distance
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_card_partitionWordCrossing_le_add_distance

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (p q : ∀ n, Equiv.Perm (V n))
    (hq : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n) (q n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0))
    (hdist : Tendsto
      (fun n => SoficGroups.normalizedHamming (p n) (q n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n) (p n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n) (q n)).card : ℝ) /
            Fintype.card (V n) +
          SoficGroups.normalizedHamming (p n) (q n))
      atTop (nhds 0) := by
    simpa using hq.add hdist
  refine squeeze_zero (fun n => by positivity) ?_ hupper
  intro n
  have hnat := card_partitionWordCrossing_le_add_distance
    (Q n) (p n) (q n)
  have hreal :
      ((SoficGroups.partitionWordCrossing (Q n) (p n)).card : ℝ) ≤
      ((SoficGroups.partitionWordCrossing (Q n) (q n)).card : ℝ) +
        (SoficGroups.permutationDistance (p n) (q n) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((SoficGroups.partitionWordCrossing (Q n) (p n)).card : ℝ) /
        Fintype.card (V n) ≤
      (((SoficGroups.partitionWordCrossing (Q n) (q n)).card : ℝ) +
        (SoficGroups.permutationDistance (p n) (q n) : ℝ)) /
          Fintype.card (V n) :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = ((SoficGroups.partitionWordCrossing (Q n) (q n)).card : ℝ) /
          Fintype.card (V n) +
        SoficGroups.normalizedHamming (p n) (q n) := by
      simp [add_div, SoficGroups.normalizedHamming,
        SoficGroups.permutationDistance]
end SoficGroups.SourceGeneratedWordCrossing
