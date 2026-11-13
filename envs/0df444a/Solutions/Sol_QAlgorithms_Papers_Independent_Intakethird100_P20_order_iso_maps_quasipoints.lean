-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.order_iso_maps_quasipoints
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:28:08.253767+00:00
-- url     : https://prove2.me/submissions/3dce199b-9138-43dd-ab35-70ade98a91dc

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {L : Type*} {K : Type*} [Lattice L] [BoundedOrder L]
    [Lattice K] [BoundedOrder K] (e : L ≃o K) (B : Set L) (hB : IsQuasipoint B) :
    IsQuasipoint (e '' B) := by
  classical
  have hbase : IsFilterBase (e '' B) := by
    refine ⟨hB.1.1.image _, ?_, ?_⟩
    · rintro ⟨a, ha, hea⟩
      have hz : a = ⊥ := e.injective (hea.trans e.map_bot.symm)
      exact hB.1.2.1 (hz ▸ ha)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hca, hcb⟩ := hB.1.2.2 a ha b hb
      exact ⟨e c, ⟨c, hc, rfl⟩, e.monotone hca, e.monotone hcb⟩
  refine ⟨hbase, ?_⟩
  intro C hC hsub
  have hpre : IsFilterBase (e ⁻¹' C) := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hC.1
      exact ⟨e.symm k, by simpa using hk⟩
    · intro h
      exact hC.2.1 (by simpa using h)
    · intro a ha b hb
      obtain ⟨c, hc, hca, hcb⟩ := hC.2.2 (e a) ha (e b) hb
      refine ⟨e.symm c, by simpa using hc, ?_, ?_⟩
      · simpa using e.symm.monotone hca
      · simpa using e.symm.monotone hcb
  have hBpre : B ⊆ e ⁻¹' C := fun a ha => hsub ⟨a, ha, rfl⟩
  have heq := hB.2 (e ⁻¹' C) hpre hBpre
  apply Set.Subset.antisymm _ hsub
  intro c hc
  refine ⟨e.symm c, ?_, e.apply_symm_apply c⟩
  rw [← heq]
  simpa using hc
