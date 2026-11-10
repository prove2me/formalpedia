-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P93.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:18:12.54719+00:00
-- url     : https://prove2.me/submissions/2a23c4ad-d490-43e1-9019-a6c308f2cd1a

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

universe u

open QAlgorithms.Papers.Independent.Intakethird100.P93 in
theorem solution {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : CrossedModule G H) {X : Type u} [TopologicalSpace X] (B : Bispace C X) :
    ((unitLevel C B).Nonempty ↔ bispaceType C B = unitType C) ∧
    ((unitLevel C B).Nonempty →
      IsReduction C B C.t.ker (⊥ : Subgroup H) (unitLevel C B)) := by
  have hreach : ∀ x y : X, ∃ g : G, B.right.act x g = y := by
    intro x y
    obtain ⟨e, he⟩ := B.torsor.2 x
    exact ⟨e.symm y, by rw [← he, e.apply_symm_apply]⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨g, hg⟩ := hreach (Classical.choice B.torsor.1) y
    have h1 := B.equivariant (Classical.choice B.torsor.1) g
    rw [hg, show B.psi y = 1 from hy] at h1
    unfold bispaceType unitType typeProjection
    rw [QuotientGroup.eq]
    have : (B.psi (Classical.choice B.torsor.1))⁻¹ = C.t g := by
      rw [inv_eq_iff_mul_eq_one]; exact h1.symm
    rw [mul_one, this]
    exact ⟨g, rfl⟩
  · intro h
    unfold bispaceType unitType typeProjection at h
    rw [QuotientGroup.eq, mul_one] at h
    obtain ⟨g, hg⟩ := h
    refine ⟨B.right.act (Classical.choice B.torsor.1) g, ?_⟩
    show B.psi (B.right.act (Classical.choice B.torsor.1) g) = 1
    rw [B.equivariant, hg, mul_inv_cancel]
  · rintro ⟨x, hx⟩
    have hx1 : B.psi x = 1 := hx
    refine ⟨⟨x, ?_⟩, fun y hy => ?_⟩
    · ext y
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hy
        have hy1 : B.psi y = 1 := hy
        obtain ⟨g, hg⟩ := hreach x y
        have h1 := B.equivariant x g
        rw [hg, hy1, hx1, one_mul] at h1
        exact ⟨⟨g, MonoidHom.mem_ker.mpr h1.symm⟩, hg⟩
      · rintro ⟨⟨k, hk⟩, rfl⟩
        show B.psi (B.right.act x k) = 1
        rw [B.equivariant, hx1, one_mul]
        exact MonoidHom.mem_ker.mp hk
    · have hy1 : B.psi y = 1 := hy
      rw [hy1]
      exact Subgroup.one_mem _
