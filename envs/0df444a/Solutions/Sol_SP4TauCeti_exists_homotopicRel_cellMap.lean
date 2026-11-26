-- Prove2me | solution 1 for SP4TauCeti.exists_homotopicRel_cellMap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T14:19:12.319377+00:00
-- url     : https://prove2.me/submissions/fd253476-550f-4535-b8b2-4fd82da5a998
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4TauCeti
import Definitions.Def_SP4TauCetiHEP
import Theorems.Thm_SP4TauCeti_exists_continuousMap_prod_skeletonLT_succ
import Theorems.Thm_SP4TauCeti_hasHomotopyExtensionProperty_skeletonLT
import Theorems.Thm_SP4TauCeti_HEP_exists_extension_of_isClosed
import Theorems.Thm_SP4TauCeti_HEP_isClosed

set_option autoImplicit false

open scoped ContinuousMap unitInterval
open ContinuousMap Metric Set Topology Topology.RelCWComplex unitInterval

universe u v

/-- The compression lemma's one-dimension step, proved by transplanting the structure of
TauCeti's `exists_homotopicRel_cellMap`: glue the cell homotopies over the closed `n`-cells to a
homotopy on `skeletonLT C (n + 1)`, then extend it to all of `C` using the homotopy extension
property of that skeleton. -/
theorem solution
    (X : Type u) [TopologicalSpace X] [T2Space X]
    (C D : Set X) [RelCWComplex C D]
    (Y : Type v) [TopologicalSpace Y]
    (n : ℕ) (f : C(C, Y))
    (ψ : cell C n → C(closedBall (0 : Fin n → ℝ) 1, Y))
    (hψ : ∀ j, (f.comp (SP4TauCeti.cellMap j)).HomotopicRel (ψ j)
        {z | (z : Fin n → ℝ) ∈ sphere 0 1}) :
    ∃ g : C(C, Y), f.HomotopicRel g {x : C | (x : X) ∈ skeletonLT C n} ∧
      ∀ j z, g (SP4TauCeti.cellMap j z) = ψ j z := by
  let H (j : cell C n) := (hψ j).some
  -- Glue the cell homotopies over the closed `n`-cells, stationary on `skeletonLT C n`.
  obtain ⟨F, hFG, hFH⟩ := SP4TauCeti.exists_continuousMap_prod_skeletonLT_succ
    (Z := I) (n := n)
    (f.comp ⟨fun p : I × (skeletonLT C n : Set X) ↦
      ⟨p.2, (skeletonLT C n).subset_complex p.2.property⟩, by fun_prop⟩)
    (fun j ↦ (H j).toContinuousMap)
    (by
      intro j t y hy
      exact ((H j).eq_fst t hy).trans (by
        change f (SP4TauCeti.cellMap j y) =
          f ⟨map n j y, (skeletonLT C n).subset_complex
            (cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩)⟩
        congr 1))
  -- `F` starts at `f`.
  have hF₀ (x : X) (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
      F (0, ⟨x, hx⟩) = f ⟨x, (skeletonLT C ((n + 1 : ℕ) : ℕ∞)).subset_complex hx⟩ := by
    have hidx : ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by norm_num
    have hxmem : (x : X) ∈ (skeletonLT C n : Set X) ∪ ⋃ j : cell C n, closedCell n j := by
      have htmp : (x : X) ∈ skeletonLT C ((n : ℕ∞) + 1) := by simpa [hidx] using hx
      rw [skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ n]
      exact htmp
    simp only [mem_union, mem_iUnion] at hxmem
    rcases hxmem with hxlt | hxcell
    · exact hFG 0 x hxlt
    · obtain ⟨j, hxj⟩ := hxcell
      rw [closedCell, mem_image] at hxj
      obtain ⟨z, hz, hzx⟩ := hxj
      let w : closedBall (0 : Fin n → ℝ) 1 := ⟨z, hz⟩
      have hFj : F (0, ⟨map n j z, by
          simpa [show ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 by norm_num] using
            (closedCell_subset_skeletonLT n j ⟨z, hz, rfl⟩)⟩) =
          (H j).toContinuousMap (0, w) := by
        simpa [w] using hFH j 0 w
      subst x
      rw [hFj]
      rw [ContinuousMap.HomotopyWith.coe_toContinuousMap, (H j).apply_zero]
      congr 1
  -- Extend `F` over `C` by the homotopy extension property of `skeletonLT C (n + 1)`.
  have hClosed : IsClosed
      (Subtype.val ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) : Set C) :=
    SP4TauCeti.HEP_isClosed
      (SP4TauCeti.hasHomotopyExtensionProperty_skeletonLT
        (X := X) (C := C) (D := D) (n + 1))
  obtain ⟨G, hG₀, hGF⟩ := SP4TauCeti.HEP_exists_extension_of_isClosed
    hClosed
    (SP4TauCeti.hasHomotopyExtensionProperty_skeletonLT
      (X := X) (C := C) (D := D) (n + 1)) f
    (F.comp ⟨fun p : I × (Subtype.val ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) : Set C) ↦
      (p.1, ⟨p.2.val, p.2.property⟩), by fun_prop⟩)
    (by
      intro a
      change F (0, ⟨a.val.val, a.property⟩) = f a.val
      exact hF₀ a.val.val a.property)
  refine ⟨⟨fun x ↦ G (1, x), by fun_prop⟩, ?_, ?_⟩
  · refine ⟨⟨⟨G, hG₀, fun _ ↦ rfl⟩, ?_⟩⟩
    intro t x hx
    exact (hGF t ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩).trans
      (hFG t (x : X) hx)
  · intro j y
    have hmem : (SP4TauCeti.cellMap j y : X) ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
      rw [SP4TauCeti.coe_cellMap_apply]
      simpa [show ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 by norm_num] using
        (closedCell_subset_skeletonLT n j ⟨y, y.property, rfl⟩)
    exact (hGF 1 ⟨SP4TauCeti.cellMap j y, hmem⟩).trans
      ((hFH j 1 y).trans (by
        rw [ContinuousMap.HomotopyWith.coe_toContinuousMap, (H j).apply_one]))
