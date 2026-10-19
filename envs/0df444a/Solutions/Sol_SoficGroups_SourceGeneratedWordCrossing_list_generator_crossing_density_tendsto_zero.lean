-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.list_generator_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/75ec18de-6afc-459a-bb56-b6f1956fa465

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_card_partitionWordCrossing_mul_le

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
    {ι : Type*}
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hgenerator : ∀ i : ι, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          (σ n i)).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (l : List ι) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((l.map (σ n)).prod)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
  induction l with
  | nil =>
      simp [SoficGroups.partitionWordCrossing]
  | cons i l ih =>
      have hupper : Tendsto
          (fun n =>
            ((SoficGroups.partitionWordCrossing (Q n)
              (σ n i)).card : ℝ) / Fintype.card (V n) +
            ((SoficGroups.partitionWordCrossing (Q n)
              ((l.map (σ n)).prod)).card : ℝ) /
                Fintype.card (V n))
          atTop (nhds 0) := by
        simpa using (hgenerator i).add ih
      refine squeeze_zero (fun n => by positivity) ?_ hupper
      intro n
      have hnat := card_partitionWordCrossing_mul_le (Q n)
        (σ n i) ((l.map (σ n)).prod)
      have hreal :
          ((SoficGroups.partitionWordCrossing (Q n)
            (σ n i * (l.map (σ n)).prod)).card : ℝ) ≤
          ((SoficGroups.partitionWordCrossing (Q n)
            (σ n i)).card : ℝ) +
          ((SoficGroups.partitionWordCrossing (Q n)
            ((l.map (σ n)).prod)).card : ℝ) := by
        exact_mod_cast hnat
      simpa [add_div] using
        (div_le_div_of_nonneg_right hreal
          (by positivity : (0 : ℝ) ≤ Fintype.card (V n)))
end SoficGroups.SourceGeneratedWordCrossing
