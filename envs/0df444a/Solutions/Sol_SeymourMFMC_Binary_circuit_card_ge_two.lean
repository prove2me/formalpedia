-- Prove2me | solution 1 for SeymourMFMC.Binary.circuit_card_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:36:45.130601+00:00
-- url     : https://prove2.me/submissions/210116d8-6c4d-41f6-bcbd-049e597f7cc3

import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsCircuit
set_option autoImplicit false
open SeymourMFMC.Binary

private theorem ground_mem_blocker {α : Type*} [DecidableEq α]
    (L : Finset (Finset α)) (hL : IsClutter L) (x : α) (hx : x ∈ ground L) :
    ∃ B ∈ blocker L, x ∈ B := by
  classical
  obtain ⟨A, hA, hxA⟩ := Finset.mem_sup.mp hx
  let T := ground L \ A.erase x
  have hT : Meets L T := by
    intro D hD
    by_contra hn
    have hDsub : D ⊆ A.erase x := by
      intro y hy
      have hyground : y ∈ ground L := Finset.mem_sup.mpr ⟨D, hD, hy⟩
      by_contra hye
      exact hn ⟨y, Finset.mem_inter.mpr ⟨hy, Finset.mem_sdiff.mpr ⟨hyground, hye⟩⟩⟩
    have heq : D = A := hL D hD A hA (hDsub.trans (Finset.erase_subset _ _))
    subst D
    have hh := hDsub hxA
    simp at hh
  obtain ⟨B, hB, hmin⟩ := WellFoundedLT.exists_minimal (inferInstance : WellFoundedLT (Finset α))
    {B : Finset α | B ⊆ T ∧ Meets L B} ⟨T, Finset.Subset.refl _, hT⟩
  have hBG : B ⊆ ground L := hB.1.trans Finset.sdiff_subset
  have hblock : B ∈ blocker L := by
    simp only [blocker, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hBG, hB.2, ?_⟩
    intro B' hB' hm
    have hs := Finset.mem_ssubsets.mp hB'
    have hbsub : B ⊆ B' := hmin ⟨hs.1.trans hB.1, hm⟩ hs.1
    exact hs.2 hbsub
  obtain ⟨y, hy⟩ := hB.2 A hA
  obtain ⟨hyA, hyB⟩ := Finset.mem_inter.mp hy
  have hyT := hB.1 hyB
  have hyx : y = x := by
    by_contra hne
    exact (Finset.mem_sdiff.mp hyT).2 (Finset.mem_erase.mpr ⟨hne, hyA⟩)
  exact ⟨B, hblock, hyx ▸ hyB⟩

theorem solution {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (C : Finset α) (hC : IsCircuit L C) :
    2 ≤ C.card := by
  have hcpos : 0 < C.card := hC.1.card_pos
  by_contra hn
  have hc1 : C.card = 1 := by omega
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc1
  have hx : x ∈ ground L := hC.2.1.1 (by simp)
  obtain ⟨B, hB, hxB⟩ := ground_mem_blocker L hL x hx
  have heven := hC.2.1.2 B hB
  simp [hxB] at heven
