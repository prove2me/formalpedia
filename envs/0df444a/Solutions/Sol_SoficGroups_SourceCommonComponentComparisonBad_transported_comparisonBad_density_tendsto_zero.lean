-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.transported_comparisonBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/ee8b6048-84bb-427a-b084-0d0f3433ad06

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_comparisonBad_card_le_overlap_and_loss
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_cast_card_sdiff_eq_sub_card_inter

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
    (T : (n : ℕ) → Equiv.Perm (V n))
    (eta : ℕ → ℝ)
    (hoverlap : Tendsto
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition (Q n) (T n))
          (Q n) (eta n), (C.card : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hloss : Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition (Q n) (T n)).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((comparisonBad (Q n) (T n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by
  have hlimit : Tendsto
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition (Q n) (T n))
          (Q n) (eta n), (C.card : ℝ)) /
            Fintype.card (V n) +
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition (Q n) (T n)).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0) := by
    simpa only [zero_add] using hoverlap.add hloss
  refine squeeze_zero (fun n => by positivity) ?_ hlimit
  intro n
  have hnat := comparisonBad_card_le_overlap_and_loss
    (Q n) (T n) (eta n)
  have hreal :
      ((comparisonBad (Q n) (T n) (eta n)).card : ℝ) ≤
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition (Q n) (T n))
          (Q n) (eta n), (C.card : ℝ)) +
        ∑ C ∈
          (SoficGroups.transportedUnivFinpartition (Q n) (T n)).parts,
          ((C \ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ) := by
    exact_mod_cast hnat
  simp_rw [cast_card_sdiff_eq_sub_card_inter] at hreal
  calc
    ((comparisonBad (Q n) (T n) (eta n)).card : ℝ) /
        Fintype.card (V n) ≤
      ((∑ C ∈ SoficGroups.insufficientOverlapComponents
        (SoficGroups.transportedUnivFinpartition (Q n) (T n))
        (Q n) (eta n), (C.card : ℝ)) +
        ∑ C ∈
          (SoficGroups.transportedUnivFinpartition (Q n) (T n)).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n) :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = _ := by ring
end SoficGroups.SourceCommonComponentComparisonBad
