-- Prove2me | solution 1 for WilliamsonShmoys.sum_component_edge_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:35:08.854636+00:00
-- url     : https://prove2.me/submissions/48ee0137-2894-48bd-921a-ece36803dda3

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (comps : Finset (Set V))
    (hne : ∀ C ∈ comps, C.Nonempty)
    (hV : 3 ≤ Fintype.card V)
    (hcard : ∑ C ∈ comps, C.ncard = Fintype.card V)
    (hlocal : ∀ C ∈ comps,
      (K.induce C).edgeSet.ncard ≤
        (if C.ncard < 3 then C.ncard - 1 else 3 * C.ncard - 6)) :
    (∑ C ∈ comps, (K.induce C).edgeSet.ncard) ≤
      3 * Fintype.card V - 6 := by
  classical
  let edgeCount : Set V → Nat := fun C => (K.induce C).edgeSet.ncard
  by_cases hm : comps.card = 1
  · obtain ⟨C, hCeq⟩ := Finset.card_eq_one.mp hm
    have hmem : C ∈ comps := by rw [hCeq]; simp
    have hsize : C.ncard = Fintype.card V := by
      simpa [hCeq] using hcard
    have hlarge : ¬ Fintype.card V < 3 := by omega
    have hloc := hlocal C hmem
    have hbound : edgeCount C ≤ 3 * Fintype.card V - 6 := by
      simpa [edgeCount, hsize, hlarge] using hloc
    simpa [hCeq, edgeCount] using hbound
  · have hnonempty : comps.Nonempty := by
      by_contra h
      have he : comps = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he] at hcard
      omega
    have hcardpos : 0 < comps.card := Finset.card_pos.mpr hnonempty
    have hmge : 2 ≤ comps.card := by omega
    have hterm : ∀ C ∈ comps, edgeCount C + 3 ≤ 3 * C.ncard := by
      intro C hC
      have hpos : 0 < C.ncard := (Set.ncard_pos).2 (hne C hC)
      have hl := hlocal C hC
      change edgeCount C ≤
        (if C.ncard < 3 then C.ncard - 1 else 3 * C.ncard - 6) at hl
      by_cases hsmall : C.ncard < 3
      · simp [hsmall] at hl
        omega
      · simp [hsmall] at hl
        omega
    have hagg :
        (∑ C ∈ comps, edgeCount C) + 3 * comps.card ≤
          3 * (∑ C ∈ comps, C.ncard) := by
      calc
        (∑ C ∈ comps, edgeCount C) + 3 * comps.card =
            (∑ C ∈ comps, edgeCount C) + (∑ C ∈ comps, (3 : Nat)) := by simp <;> omega
        _ = ∑ C ∈ comps, (edgeCount C + 3) := by
          rw [Finset.sum_add_distrib]
        _ ≤ ∑ C ∈ comps, 3 * C.ncard := Finset.sum_le_sum hterm
        _ = 3 * (∑ C ∈ comps, C.ncard) := by simp [Finset.mul_sum]
    rw [hcard] at hagg
    change (∑ C ∈ comps, edgeCount C) ≤ 3 * Fintype.card V - 6
    omega
