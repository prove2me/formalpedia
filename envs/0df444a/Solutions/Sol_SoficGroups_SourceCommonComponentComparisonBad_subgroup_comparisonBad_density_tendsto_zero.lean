-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.subgroup_comparisonBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/e8882017-f854-4447-b279-7ffd661d7cd9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_comparisonBad_subset_partitionWordCrossing

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
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (p : (n : ℕ) → Equiv.Perm (V n))
    (eta : ℕ → ℝ) (heta : ∀ n, 0 ≤ eta n)
    (hcross : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n) (p n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((comparisonBad (Q n) (p n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => by positivity) ?_ hcross
  intro n
  have hnat := Finset.card_le_card
    (comparisonBad_subset_partitionWordCrossing
      (Q n) (p n) (eta n) (heta n))
  have hreal :
      ((comparisonBad (Q n) (p n) (eta n)).card : ℝ) ≤
        ((SoficGroups.partitionWordCrossing
          (Q n) (p n)).card : ℝ) := by
    exact_mod_cast hnat
  exact div_le_div_of_nonneg_right hreal (by positivity)
end SoficGroups.SourceCommonComponentComparisonBad
