-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.combined_positive_comparisonBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/49fc0fd9-fa67-49a6-ba64-071271357b62

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_familyComparisonBad_card
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_subgroup_comparisonBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_transported_comparisonBad_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonComponentComparisonBad
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (ι κ : Type*) [Fintype ι] [Fintype κ]
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (eta : ℕ → ℝ) (heta : ∀ n, 0 ≤ eta n)
    (hcross : ∀ i : ι, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing
          (Q n) (σ n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hoverlap : ∀ j : κ, Tendsto
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition
            (Q n) (T n j)) (Q n) (eta n), (C.card : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0))
    (hloss : ∀ j : κ, Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition
            (Q n) (T n j)).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((familyComparisonBad (Q n)
          (Sum.elim (σ n) (T n)) (eta n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
  classical
  have hsingle (i : ι ⊕ κ) : Tendsto
      (fun n =>
        ((comparisonBad (Q n)
          (Sum.elim (σ n) (T n) i) (eta n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
    cases i with
    | inl i =>
        exact subgroup_comparisonBad_density_tendsto_zero
          V Q (fun n => σ n i) eta heta (hcross i)
    | inr j =>
        exact transported_comparisonBad_density_tendsto_zero
          V Q (fun n => T n j) eta (hoverlap j) (hloss j)
  have hsum : Tendsto
      (fun n => ∑ i : ι ⊕ κ,
        ((comparisonBad (Q n)
          (Sum.elim (σ n) (T n) i) (eta n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
    simpa using
      tendsto_finsetSum Finset.univ (fun i _ => hsingle i)
  have hrewrite (n : ℕ) :
      ((familyComparisonBad (Q n)
        (Sum.elim (σ n) (T n)) (eta n)).card : ℝ) /
          Fintype.card (V n) =
        ∑ i : ι ⊕ κ,
          ((comparisonBad (Q n)
            (Sum.elim (σ n) (T n) i) (eta n)).card : ℝ) /
              Fintype.card (V n) := by
    rw [familyComparisonBad_card]
    push_cast
    rw [Finset.sum_div]
  simpa only [hrewrite] using hsum
end SoficGroups.SourceCommonComponentComparisonBad
