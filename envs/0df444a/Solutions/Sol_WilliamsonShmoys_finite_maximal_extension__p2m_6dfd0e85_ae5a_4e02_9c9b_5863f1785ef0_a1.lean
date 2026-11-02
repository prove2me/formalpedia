-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:21:39.333227+00:00
-- url     : https://prove2.me/submissions/8a466697-8cf6-47af-b466-e3db9f5a9bd9

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α]
    (R : α → α → Prop) (μ : α → Nat) (P : α → Prop)
    (hrefl : ∀ x, R x x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (hgrowth : ∀ x y, R x y → x ≠ y → μ x < μ y)
    (x : α) (hx : P x) :
    ∃ y, R x y ∧ P y ∧ ∀ z, R y z → P z → z = y := by
  classical
  let s : Finset α := Finset.univ.filter fun y => R x y ∧ P y
  have hs : s.Nonempty := by
    refine ⟨x, ?_⟩
    simp [s, hrefl x, hx]
  let t : Finset Nat := s.image μ
  have ht : t.Nonempty := Finset.image_nonempty.mpr hs
  let m : Nat := t.max' ht
  have hm : m ∈ t := by
    exact Finset.max'_mem t ht
  rcases Finset.mem_image.mp hm with ⟨y, hy, hμy⟩
  refine ⟨y, (Finset.mem_filter.mp hy).2.1, (Finset.mem_filter.mp hy).2.2, ?_⟩
  intro z hyz hpz
  have hxz : R x z := htrans x y z (Finset.mem_filter.mp hy).2.1 hyz
  have hz : z ∈ s := by
    simp [s, hxz, hpz]
  have hzimg : μ z ∈ t := Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hle : μ z ≤ m := by
    change μ z ≤ t.max' ht
    exact Finset.le_max' t (μ z) hzimg
  by_contra hne
  have hlt : m < μ z := by
    simpa [hμy] using hgrowth y z hyz (fun h => hne h.symm)
  exact (not_lt_of_ge hle) hlt