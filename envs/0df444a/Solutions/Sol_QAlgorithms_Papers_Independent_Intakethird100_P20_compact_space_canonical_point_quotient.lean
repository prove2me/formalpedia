-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.compact_space_canonical_point_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:36:21.903197+00:00
-- url     : https://prove2.me/submissions/3392b9ae-bbef-4bcc-8ba8-c64cbb1b75f0

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_compact_open_quasipoint_unique_point
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_exists_open_quasipoint_over
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_quasipoint_cluster_characterization
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_lattice_stone_compact
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Corollary 3.5; de Groote, Observables I, PDF p./pp. 56.
-/
theorem solution {M : Type u} [TopologicalSpace M] [CompactSpace M] [T2Space M] :
    ∃ pt : StoneSpectrum (Opens M) → M,
      (∀ B, LiesOver B (pt B)) ∧ Function.Surjective pt ∧
        Continuous pt ∧ Topology.IsQuotientMap pt := by
  classical
  have hex (B : StoneSpectrum (Opens M)) : ∃ x : M, LiesOver B x :=
    (compact_open_quasipoint_unique_point B).exists
  let pt : StoneSpectrum (Opens M) → M := fun B => Classical.choose (hex B)
  have hpt (B : StoneSpectrum (Opens M)) : LiesOver B (pt B) := Classical.choose_spec (hex B)
  have hsurj : Function.Surjective pt := by
    intro x
    obtain ⟨B, hBx⟩ := exists_open_quasipoint_over x
    exact ⟨B, (compact_open_quasipoint_unique_point B).unique (hpt B) hBx⟩
  have ht := stone_topology_properties (L := Opens M)
  have hcont : Continuous pt := by
    apply continuous_def.mpr
    intro V hV
    apply isOpen_iff_mem_nhds.mpr
    intro B hB
    obtain ⟨W, ⟨hBW, hWopen⟩, hWsub⟩ :=
      (hasBasis_opens_closure (pt B)).mem_iff.mp (hV.mem_nhds hB)
    let U : Opens M := ⟨W, hWopen⟩
    have hUB : U ∈ B.val :=
      (open_quasipoint_cluster_characterization B (pt B)).2.mp (hpt B) U hBW
    apply Filter.mem_of_superset (((ht.2.2.2.1 U).2).mem_nhds hUB)
    intro C hUC
    have hcI := (open_quasipoint_cluster_characterization C (pt C)).1.mp (hpt C)
    have hcU := Set.mem_iInter.mp hcI (⟨U, hUC⟩ : {U : Opens M // U ∈ C.val})
    exact hWsub hcU
  letI : CompactSpace (StoneSpectrum (Opens M)) := open_lattice_stone_compact
  have hclosed : IsClosedMap pt := hcont.isClosedMap
  exact ⟨pt, hpt, hsurj, hcont, hclosed.isQuotientMap hcont hsurj⟩
