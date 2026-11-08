-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.filter_base_extends_to_quasipoint
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:36:18.013704+00:00
-- url     : https://prove2.me/submissions/ba83801c-b04c-4c5e-a640-07502b663b33

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

open QAlgorithms.Papers.Independent.Intakethird100.P20 in
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] (B : Set L) (hB : IsFilterBase B) :
    ∃ C : Set L, IsQuasipoint C ∧ B ⊆ C := by
  have H : ∀ c ⊆ {C : Set L | IsFilterBase C}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {C : Set L | IsFilterBase C}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain hne
    obtain ⟨s0, hs0⟩ := hne
    have hf : ∀ s ∈ c, IsFilterBase s := fun s hs => hc hs
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := (hf s0 hs0).1
      exact ⟨x, s0, hs0, hx⟩
    · rintro ⟨s, hs, hbot⟩
      exact (hf s hs).2.1 hbot
    · rintro a ⟨s1, hs1, ha⟩ b ⟨s2, hs2, hb⟩
      rcases hchain.total hs1 hs2 with h | h
      · obtain ⟨z, hz, hza, hzb⟩ := (hf s2 hs2).2.2 a (h ha) b hb
        exact ⟨z, ⟨s2, hs2, hz⟩, hza, hzb⟩
      · obtain ⟨z, hz, hza, hzb⟩ := (hf s1 hs1).2.2 a ha b (h hb)
        exact ⟨z, ⟨s1, hs1, hz⟩, hza, hzb⟩
  obtain ⟨m, hBm, hmax⟩ := zorn_subset_nonempty {C : Set L | IsFilterBase C} H B hB
  refine ⟨m, ⟨hmax.prop, fun C hC hmC => ?_⟩, hBm⟩
  exact (hmax.eq_of_le hC hmC).symm
