-- Prove2me | solution 1 for PaigeTarjan.Coarsest.stableWrt_union
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T06:38:49.96071+00:00
-- url     : https://prove2.me/submissions/83c646a1-0947-4d70-9a8a-fcc7102a65d2

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

open PaigeTarjan.Coarsest

/-- Property (2), p. 978: stability is inherited under union — a partition that is stable with
respect to two sets is also stable with respect to their union.

The whole content is the set identity `E⁻¹(S ∪ T) = E⁻¹(S) ∪ E⁻¹(T)`, proved once below. Each
block `B` of `P` is then stable with respect to `S ∪ T` in one of two ways: if it sits wholly in
`E⁻¹(S)` or wholly in `E⁻¹(T)` it sits wholly in the union, and if it misses both preimages it
misses the union too. -/
theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (S T : Finset U)
    (hP : IsPartition P) (hS : StableWrt E P S) (hT : StableWrt E P T) :
    StableWrt E P (S ∪ T) := by
  -- `x ∈ E⁻¹(S ∪ T)` exactly when `x` has a witness in `S` or in `T`.
  have hpre : preimage E (S ∪ T) = preimage E S ∪ preimage E T := by
    unfold preimage
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rcases hy with hyS | hyT
      · exact Or.inl ⟨y, hyS, hxy⟩
      · exact Or.inr ⟨y, hyT, hxy⟩
    · rintro (⟨y, hyS, hxy⟩ | ⟨y, hyT, hxy⟩)
      · exact ⟨y, Or.inl hyS, hxy⟩
      · exact ⟨y, Or.inr hyT, hxy⟩
  intro B hB
  rcases hS B hB with hBS | hBS
  · exact Or.inl (by
    intro x hx
    rw [hpre, Finset.mem_union]
    exact Or.inl (hBS hx))
  · rcases hT B hB with hBT | hBT
    · exact Or.inl (by
      intro x hx
      rw [hpre, Finset.mem_union]
      exact Or.inr (hBT hx))
    · exact Or.inr (by
      refine (Finset.disjoint_left.mpr ?_)
      intro x hxB hxU
      rw [hpre, Finset.mem_union] at hxU
      rcases hxU with hxS | hxT
      · exact (Finset.disjoint_left.mp hBS hxB) hxS
      · exact (Finset.disjoint_left.mp hBT hxB) hxT)
