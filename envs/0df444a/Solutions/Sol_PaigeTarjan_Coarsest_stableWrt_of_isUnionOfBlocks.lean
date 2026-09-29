-- Prove2me | solution 1 for PaigeTarjan.Coarsest.stableWrt_of_isUnionOfBlocks
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T09:09:46.509457+00:00
-- url     : https://prove2.me/submissions/9b8b43f4-80a5-42f1-9554-44e65b8cca34

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

open PaigeTarjan.Coarsest

theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U))
    (hQ : IsPartition Q) (hstab : Stable E Q) (T : Finset (Finset U)) (hT : T ⊆ Q) :
    StableWrt E Q (T.biUnion id) := by
  intro B hB
  by_cases h : ∃ C ∈ T, B ⊆ preimage E C
  · left
    obtain ⟨C, hC, hBC⟩ := h
    intro x hxB
    obtain ⟨_, y, hyC, hxy⟩ := Finset.mem_filter.mp (hBC hxB)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, y, ?_, hxy⟩
    exact Finset.mem_biUnion.mpr ⟨C, hC, hyC⟩
  · right
    apply Finset.disjoint_left.mpr
    intro x hxB hxPre
    obtain ⟨_, y, hyUnion, hxy⟩ := Finset.mem_filter.mp hxPre
    obtain ⟨C, hC, hyC⟩ := Finset.mem_biUnion.mp hyUnion
    rcases hstab C (hT hC) B hB with hBC | hdisj
    · exact h ⟨C, hC, hBC⟩
    · apply (Finset.disjoint_left.mp hdisj) hxB
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, y, hyC, hxy⟩
