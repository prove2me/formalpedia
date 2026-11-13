-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.compact_connected_point_map_not_open
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:39:05.26019+00:00
-- url     : https://prove2.me/submissions/9145c8e2-4ff6-4268-83d0-7ae36d2483ef

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_compact_space_canonical_point_quotient
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_lattice_stone_compact
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- compact-point-map-not-open; de Groote, Observables I, PDF p./pp. 56, 57.
-/
theorem solution {M : Type u} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [Nontrivial M] :
    ∃ pt : StoneSpectrum (Opens M) → M, (∀ B, LiesOver B (pt B)) ∧
      Continuous pt ∧ Function.Surjective pt ∧ IsClosedMap pt ∧ ¬ IsOpenMap pt := by
  classical
  letI : CompactSpace (StoneSpectrum (Opens M)) := open_lattice_stone_compact
  obtain ⟨pt, hpt, hsurj, hcont, _⟩ := compact_space_canonical_point_quotient (M := M)
  have hclosed : IsClosedMap pt := hcont.isClosedMap
  refine ⟨pt, hpt, hcont, hsurj, hclosed, ?_⟩
  intro hopen
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  obtain ⟨B, hBx⟩ := hsurj x
  have hpre : IsOpen (pt ⁻¹' (({y} : Set M)ᶜ)) :=
    (isClosed_singleton : IsClosed ({y} : Set M)).isOpen_compl.preimage hcont
  have hBpre : B ∈ pt ⁻¹' (({y} : Set M)ᶜ) := by
    change pt B ≠ y
    rw [hBx]
    exact hxy
  have ht := stone_topology_properties (L := Opens M)
  obtain ⟨_, ⟨U, rfl⟩, hBU, hsub⟩ := ht.2.2.2.2.1.exists_subset_of_mem_open hBpre hpre
  have hclopen : IsClopen (pt '' stoneBasic U) :=
    ⟨hclosed _ (ht.2.2.2.1 U).1, hopen _ (ht.2.2.2.1 U).2⟩
  have hfull : pt '' stoneBasic U = Set.univ := hclopen.eq_univ ⟨pt B, B, hBU, rfl⟩
  have hy : y ∈ pt '' stoneBasic U := by rw [hfull]; exact Set.mem_univ y
  obtain ⟨C, hCU, hCy⟩ := hy
  exact (hsub hCU) (Set.mem_singleton_iff.mpr hCy)
