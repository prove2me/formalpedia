-- Prove2me | solution 1 for OnlineTaxiRouting.Integrality.relax_eq_flow_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:47:00.14558+00:00
-- url     : https://prove2.me/submissions/d076d28c-f79a-49be-8cb3-3707a43566f0

import Mathlib
import Definitions.Def_OnlineTaxiRouting_Integrality_Setting
set_option autoImplicit false
open OnlineTaxiRouting.Integrality

theorem solution {C K : Type*} [Fintype C] [Fintype K]
    (I : Instance C K) (hfix : ∀ c, I.tmin c = I.tmax c) :
    relax I = {v | (v.1, v.2.1, v.2.2.1) ∈
        flowRelax (fun c' c => I.T c' c ≤ I.tmin c - I.tmin c')
          (fun k c => I.tinit k + I.Tk k c ≤ I.tmin c) ∧
      v.2.2.2 = I.tmin} := by
  ext v
  simp only [relax, flowRelax, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have ht : v.2.2.2 = I.tmin := by
      funext c
      have := h12 c
      rw [← hfix c] at this
      exact le_antisymm this.2 this.1
    refine ⟨⟨h6, h7, h8, h9, h10, h11, ?_, ?_⟩, ht⟩
    · intro c' c hn
      have h := h13 c c'
      rw [ht, ← hfix c'] at h
      have hlt : I.tmin c - I.tmin c' < I.T c' c := not_le.mp hn
      have hx := (h9 c' c).1
      by_contra hne
      have hpos : 0 < v.1 c' c := lt_of_le_of_ne hx (Ne.symm hne)
      nlinarith [mul_pos (sub_pos.mpr hlt) hpos]
    · intro k c hn
      have h := h14 c k
      rw [ht] at h
      have hlt : I.tmin c < I.tinit k + I.Tk k c := not_le.mp hn
      have hy := (h10 k c).1
      by_contra hne
      have hpos : 0 < v.2.1 k c := lt_of_le_of_ne hy (Ne.symm hne)
      nlinarith [mul_pos (sub_pos.mpr hlt) hpos]
  · rintro ⟨⟨h6, h7, h8, h9, h10, h11, hA, hB⟩, ht⟩
    refine ⟨h6, h7, h8, h9, h10, h11, ?_, ?_, ?_⟩
    · intro c
      rw [ht, ← hfix c]
      exact ⟨le_refl _, le_refl _⟩
    · intro c c'
      rw [ht, ← hfix c']
      by_cases hA' : I.T c' c ≤ I.tmin c - I.tmin c'
      · nlinarith [mul_nonneg (sub_nonneg.mpr hA') (h9 c' c).1]
      · have := hA c' c hA'
        rw [this]; simp
    · intro c k
      rw [ht]
      by_cases hB' : I.tinit k + I.Tk k c ≤ I.tmin c
      · nlinarith [mul_nonneg (sub_nonneg.mpr hB') (h10 k c).1]
      · have := hB k c hB'
        rw [this]; simp
