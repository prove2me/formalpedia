-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.sum_generator_crossing_eq_sum_partition_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/a4236841-f6ce-447d-a420-2452c63b4933

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sum_card_inter_partition

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) :
    (∑ i : ι, (SoficGroups.partitionWordCrossing Q (σ i)).card) =
      ∑ C ∈ Q.parts, SoficGroups.boundary σ C := by
  classical
  have hpart (i : ι) (C : Finset V) (hC : C ∈ Q.parts) :
      C ∩ SoficGroups.partitionWordCrossing Q (σ i) =
        C.filter (fun x => σ i x ∉ C) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter,
      SoficGroups.partitionWordCrossing, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hcross⟩
      refine ⟨hx, ?_⟩
      simpa [Q.part_eq_of_mem hC hx] using hcross
    · rintro ⟨hx, hcross⟩
      refine ⟨hx, ?_⟩
      simpa [Q.part_eq_of_mem hC hx] using hcross
  calc
    (∑ i : ι, (SoficGroups.partitionWordCrossing Q (σ i)).card) =
      ∑ i : ι, ∑ C ∈ Q.parts,
        (C.filter (fun x => σ i x ∉ C)).card := by
      apply Finset.sum_congr rfl
      intro i _
      have hsum := SoficGroups.sum_card_inter_partition Q
        (SoficGroups.partitionWordCrossing Q (σ i))
      simp only [Finset.univ_inter] at hsum
      calc
        (SoficGroups.partitionWordCrossing Q (σ i)).card =
            ∑ C ∈ Q.parts,
              (C ∩ SoficGroups.partitionWordCrossing Q (σ i)).card :=
          hsum.symm
        _ = ∑ C ∈ Q.parts,
              (C.filter (fun x => σ i x ∉ C)).card := by
          apply Finset.sum_congr rfl
          intro C hC
          rw [hpart i C hC]
    _ = ∑ C ∈ Q.parts,
        ∑ i : ι, (C.filter (fun x => σ i x ∉ C)).card := by
      rw [Finset.sum_comm]
    _ = ∑ C ∈ Q.parts, SoficGroups.boundary σ C := by
      simp [SoficGroups.boundary]
end SoficGroups.SourceGeneratedWordCrossing
