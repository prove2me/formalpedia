-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.closure_of_basic_union
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:12:18.91165+00:00
-- url     : https://prove2.me/submissions/b9cd9bd3-8f69-4784-8fb7-226ee2efdae3

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stoneBasic_nonempty_iff
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- closure-basic-union; de Groote, Observables I, PDF p./pp. 45.
-/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] (s : Set L) (B : StoneSpectrum L) :
    (B ∈ closure (⋃ a ∈ s, stoneBasic a) ↔ ∀ b ∈ B.val, ∃ a ∈ s, b ⊓ a ≠ ⊥) := by
  classical
  have ht := stone_topology_properties (L := L)
  have hb := ht.2.2.2.2.1
  have hm := ht.1
  rw [hb.mem_closure_iff]
  constructor
  · intro h b hbB
    obtain ⟨C, hcb, hcs⟩ := h (stoneBasic b) ⟨b, rfl⟩ hbB
    obtain ⟨a, ha, hca⟩ := Set.mem_iUnion₂.mp hcs
    refine ⟨a, ha, (stoneBasic_nonempty_iff (b ⊓ a)).mp ?_⟩
    exact ⟨C, (hm b a).symm ▸ (show C ∈ stoneBasic b ∩ stoneBasic a from ⟨hcb, hca⟩)⟩
  · intro h o ho hBo
    obtain ⟨b, rfl⟩ := ho
    obtain ⟨a, ha, hba⟩ := h b hBo
    obtain ⟨C, hc⟩ := (stoneBasic_nonempty_iff (b ⊓ a)).mpr hba
    have hp : C ∈ stoneBasic b ∩ stoneBasic a := hm b a ▸ hc
    exact ⟨C, hp.1, Set.mem_iUnion₂.mpr ⟨a, ha, hp.2⟩⟩
