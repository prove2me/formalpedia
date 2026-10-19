-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_subset_partitionWordCrossing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/50dea087-df96-4987-a2fa-7fa38ea9dabd

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonComponentComparisonBad
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : Equiv.Perm V) (eta : ℝ) (heta : 0 ≤ eta) :
    comparisonBad Q p eta ⊆ SoficGroups.partitionWordCrossing Q p := by
  classical
  intro x hx
  unfold comparisonBad at hx
  have hbad := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ x, ?_⟩
  intro hsame
  apply hbad
  have hpart : Q.part (p x) = Q.part x :=
    Q.part_eq_of_mem (Q.part_mem.mpr (Finset.mem_univ x)) hsame
  have hsize : SoficGroups.partitionComponentSize Q (p x) =
      SoficGroups.partitionComponentSize Q x := by
    unfold SoficGroups.partitionComponentSize
    rw [hpart]
  rw [hsize]
  have hnonneg : (0 : ℝ) ≤
      (SoficGroups.partitionComponentSize Q x : ℝ) := by
    positivity
  nlinarith
end SoficGroups.SourceCommonComponentComparisonBad
