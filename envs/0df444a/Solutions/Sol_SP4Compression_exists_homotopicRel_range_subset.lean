-- Prove2me | solution 1 for SP4Compression.exists_homotopicRel_range_subset
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T12:50:34.431269+00:00
-- url     : https://prove2.me/submissions/fa4d4463-facb-4b89-88b1-656142e54530
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4Compression
import Definitions.Def_SP4TauCeti
import Theorems.Thm_SP4TauCeti_compressionHyp_of_cellCompressible
import Theorems.Thm_SP4TauCeti_exists_homotopicRel_cellMap
import Theorems.Thm_SP4TauCeti_exists_homotopicRel_forall_mapsTo_skeletonLT

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap Metric Set Topology Topology.RelCWComplex

universe u v

/-- The compression lemma, proved by transplanting the structure of TauCeti's proof.
The three genuinely topological inputs are open children; everything else (the cell-by-cell
compression step, the skeleton gluing bookkeeping, and the final range argument) is proved here. -/
theorem solution
    (X : Type u) [TopologicalSpace X] [T2Space X]
    (C D : Set X) [RelCWComplex C D]
    (Y : Type v) [TopologicalSpace Y] (y : Y)
    (hcell : SP4Compression.CellCompressible Y y)
    (f : C(C, Y)) (hf : MapsTo f {x : C | (x : X) ∈ D} {y}) :
    ∃ g : C(C, Y), f.HomotopicRel g {x : C | (x : X) ∈ D} ∧ range g ⊆ {y} := by
  -- The compression criterion, in the closed-ball model of the CW characteristic maps.
  have hcomp := SP4TauCeti.compressionHyp_of_cellCompressible Y y hcell

  -- A map sending `skeletonLT C n` into `{y}` can be compressed one dimension further.
  have step (n : ℕ) (g : C(C, Y))
      (hg : MapsTo g {x : C | (x : X) ∈ skeletonLT C n} {y}) :
      ∃ g' : C(C, Y), g.HomotopicRel g' {x : C | (x : X) ∈ skeletonLT C n} ∧
        MapsTo g' {x : C | (x : X) ∈ skeletonLT C ((n + 1 : ℕ) : ℕ∞)} {y} := by
    have hc (j : cell C n) : ∃ ψj : C(closedBall (0 : Fin n → ℝ) 1, Y),
        (g.comp (SP4TauCeti.cellMap j)).HomotopicRel ψj
            {z | (z : Fin n → ℝ) ∈ sphere 0 1} ∧ range ψj ⊆ {y} :=
      hcomp n (g.comp (SP4TauCeti.cellMap j)) (by
        intro z hz
        exact hg (by
          change ((SP4TauCeti.cellMap j z : C) : X) ∈ skeletonLT C n
          simpa [SP4TauCeti.coe_cellMap_apply] using
            cellFrontier_subset_skeletonLT n j ⟨z, hz, rfl⟩))
    choose ψ hψ hψB using hc
    obtain ⟨g', hgg', hg'⟩ := SP4TauCeti.exists_homotopicRel_cellMap n g ψ hψ
    refine ⟨g', hgg', ?_⟩
    intro x hx
    have hidx : ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by norm_num
    have hxmem : (x : X) ∈ (skeletonLT C n : Set X) ∪ ⋃ j : cell C n, closedCell n j := by
      have htmp : (x : X) ∈ skeletonLT C ((n : ℕ∞) + 1) := by
        simpa [hidx] using hx
      rw [skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ n]
      exact htmp
    simp only [mem_union, mem_iUnion] at hxmem
    rcases hxmem with hxlt | hxcell
    · exact hgg'.fst_eq_snd hxlt ▸ hg hxlt
    · obtain ⟨j, hxj⟩ := hxcell
      rw [closedCell, mem_image] at hxj
      obtain ⟨z, hz, hzx⟩ := hxj
      let w : closedBall (0 : Fin n → ℝ) 1 := ⟨z, hz⟩
      have hxeq : SP4TauCeti.cellMap j w = x := by
        apply Subtype.ext
        exact hzx
      have hg'x : g' x = ψ j w := by
        simpa [hxeq] using hg' j w
      rw [hg'x]
      exact hψB j ⟨w, rfl⟩

  -- Concatenate the successive improvements over all skeleta.
  obtain ⟨g, hg, hfg⟩ := SP4TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT
    (fun _ ↦ ({y} : Set Y)) step f hf

  -- Every point lies in some skeleton, hence in `{y}`.
  refine ⟨g, hfg, ?_⟩
  rintro z ⟨x, rfl⟩
  have hxC : (x : X) ∈ C := x.property
  have hi : (x : X) ∈ ⋃ n : ℕ, (skeletonLT C n : Set X) := by
    rw [iUnion_skeletonLT_eq_complex]
    exact hxC
  simp only [mem_iUnion] at hi
  obtain ⟨n, hn⟩ := hi
  exact hg n hn
