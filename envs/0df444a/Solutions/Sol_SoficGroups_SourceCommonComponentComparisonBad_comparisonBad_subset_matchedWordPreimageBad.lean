-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_subset_matchedWordPreimageBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/3959fcac-5fda-4774-af33-97af2b5623ce

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_partitionComponentSize_transport_lower_of_retained

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
    (T : Equiv.Perm V) (eta : ℝ) :
    comparisonBad Q T eta ⊆
      SoficGroups.matchedWordPreimageBad
        (Finset.univ : Finset V)
        (overlapRetainedComponents Q T eta)
        (SoficGroups.maximumOverlapPart Q) T := by
  classical
  intro x hx
  have hbad : ¬ (1 - eta) *
        (SoficGroups.partitionComponentSize Q x : ℝ) ≤
      (SoficGroups.partitionComponentSize Q (T x) : ℝ) := by
    unfold comparisonBad at hx
    exact (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ x, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ (T x), ?_⟩⟩
  intro hcore
  obtain ⟨C, hC, hy⟩ := Finset.mem_biUnion.mp hcore
  have hparts : C ∈
      (SoficGroups.transportedUnivFinpartition Q T).parts :=
    (Finset.mem_sdiff.mp hC).1
  have hret : C ∉ SoficGroups.insufficientOverlapComponents
      (SoficGroups.transportedUnivFinpartition Q T) Q eta :=
    (Finset.mem_sdiff.mp hC).2
  have hyC : T x ∈ C := (Finset.mem_inter.mp hy).1
  have hyD : T x ∈ SoficGroups.maximumOverlapPart Q C :=
    (Finset.mem_inter.mp hy).2
  have hxpart : Q.part x ∈ Q.parts :=
    Q.part_mem.mpr (Finset.mem_univ x)
  have hmap : (Q.part x).map T.toEmbedding ∈
      (SoficGroups.transportedUnivFinpartition Q T).parts := by
    rw [SoficGroups.transportedUnivFinpartition_parts]
    exact Finset.mem_image_of_mem
      (fun D : Finset V => D.map T.toEmbedding) hxpart
  have hyMap : T x ∈ (Q.part x).map T.toEmbedding :=
    Finset.mem_map.mpr
      ⟨x, Q.mem_part (Finset.mem_univ x), rfl⟩
  have heq : (Q.part x).map T.toEmbedding = C := by
    have hfirst :=
      (SoficGroups.transportedUnivFinpartition Q T).part_eq_of_mem
        hmap hyMap
    have hsecond :=
      (SoficGroups.transportedUnivFinpartition Q T).part_eq_of_mem
        hparts hyC
    exact hfirst.symm.trans hsecond
  apply hbad
  apply SoficGroups.partitionComponentSize_transport_lower_of_retained
    Q T (Q.part x) hxpart eta
  · simpa only [heq] using hret
  · exact Q.mem_part (Finset.mem_univ x)
  · simpa only [heq] using hyD
end SoficGroups.SourceCommonComponentComparisonBad
