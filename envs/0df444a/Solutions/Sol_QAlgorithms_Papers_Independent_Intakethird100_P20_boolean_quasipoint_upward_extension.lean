-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.boolean_quasipoint_upward_extension
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:48:29.954538+00:00
-- url     : https://prove2.me/submissions/ddfb06e3-54d8-4132-b60d-4c9d58990ca7

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutation_symmetric_iff_orthomodular
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- boolean-filter-upward-extension; de Groote, Observables I, PDF p./pp. 69.
-/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L)
    (horth : IsOrthomodular perp) (B : Set L) (hB : IsBooleanQuasipoint perp B)
    (c : L) (hcomm : ∀ a ∈ B, LatticeCommutes perp a c)
    (habove : ∃ b ∈ B, b ≤ c) : c ∈ B := by
  have hsym := (commutation_symmetric_iff_orthomodular perp horth.1).mpr horth
  obtain ⟨b0, hb0, hb0c⟩ := habove
  obtain ⟨hne, hbot, hdir⟩ := hB.1.1
  have hcne : c ≠ ⊥ := by
    intro h
    apply hbot
    have hh : b0 = ⊥ := le_bot_iff.mp (h ▸ hb0c)
    exact hh ▸ hb0
  have hbase : IsFilterBase (B ∪ {c}) := by
    refine ⟨⟨b0, Or.inl hb0⟩, ?_, ?_⟩
    · simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
      exact ⟨hbot, fun h => hcne h.symm⟩
    · intro x hx y hy
      simp only [Set.mem_union, Set.mem_singleton_iff] at hx hy ⊢
      rcases hx with hxB | hxC
      · rcases hy with hyB | hyC
        · obtain ⟨z, hz, hzx, hzy⟩ := hdir x hxB y hyB
          exact ⟨z, Or.inl hz, hzx, hzy⟩
        · subst y
          obtain ⟨z, hz, hzx, hzb⟩ := hdir x hxB b0 hb0
          exact ⟨z, Or.inl hz, hzx, hzb.trans hb0c⟩
      · subst x
        rcases hy with hyB | hyC
        · obtain ⟨z, hz, hzb, hzy⟩ := hdir b0 hb0 y hyB
          exact ⟨z, Or.inl hz, hzb.trans hb0c, hzy⟩
        · subst y
          exact ⟨c, Or.inr rfl, le_rfl, le_rfl⟩
  have hpair : ∀ x ∈ B ∪ {c}, ∀ y ∈ B ∪ {c}, LatticeCommutes perp x y := by
    intro x hx y hy
    simp only [Set.mem_union, Set.mem_singleton_iff] at hx hy
    rcases hx with hxB | hxC
    · rcases hy with hyB | hyC
      · exact hB.1.2 x hxB y hyB
      · subst y
        exact hcomm x hxB
    · subst x
      rcases hy with hyB | hyC
      · exact hsym y c (hcomm y hyB)
      · subst y
        unfold LatticeCommutes
        rw [inf_idem, (horth.1.1 c).1, sup_bot_eq]
  have hCB : B ∪ {c} = B := hB.2 (B ∪ {c}) ⟨hbase, hpair⟩ Set.subset_union_left
  have hmem : c ∈ B ∪ {c} := Set.mem_union_right _ (Set.mem_singleton c)
  rwa [hCB] at hmem
