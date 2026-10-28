-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_face_data_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:32:01.8758+00:00
-- url     : https://prove2.me/submissions/b13f4daa-4c71-469b-b9a7-8abb2cf62b5d

import Mathlib
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (parts : Finset (Finset V))
    (hV : 3 ≤ Fintype.card V)
    (hNonempty : ∀ C ∈ parts, C.Nonempty)
    (hDisjoint : ∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D)
    (hCover : parts.biUnion id = Finset.univ)
    (hEdgeSum : G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard)
    (hLocal : ∀ C ∈ parts,
      (G.induce (fun v => v ∈ C)).Connected ∧
      (if 3 ≤ C.card then
        ∃ f : ℕ,
          C.card + f = (G.induce (fun v => v ∈ C)).edgeSet.ncard + 2 ∧
          3 * f ≤ 2 * (G.induce (fun v => v ∈ C)).edgeSet.ncard
      else
        (G.induce (fun v => v ∈ C)).edgeSet.ncard ≤ 3 * C.card - 3)) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  set e : Finset V → ℕ := fun C => (G.induce (fun v => v ∈ C)).edgeSet.ncard with he
  have hcard : ∑ C ∈ parts, C.card = Fintype.card V := by
    rw [← Finset.card_univ, ← hCover, Finset.card_biUnion]
    · rfl
    · intro x hx y hy hxy; exact hDisjoint x hx y hy hxy
  have hloc : ∀ C ∈ parts, e C + 3 + (if 3 ≤ C.card then 3 else 0) ≤ 3 * C.card := by
    intro C hC
    have h1 := (hLocal C hC).2
    have hne := (hNonempty C hC).card_pos
    split_ifs at h1 ⊢ with h
    · obtain ⟨f, hf1, hf2⟩ := h1
      simp only [he]; omega
    · simp only [he]; omega
  have hsum := Finset.sum_le_sum hloc
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcard] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  have hkey : 6 ≤ parts.card * 3 + ∑ C ∈ parts, (if 3 ≤ C.card then 3 else 0) := by
    by_cases hbig : ∃ C ∈ parts, 3 ≤ C.card
    · obtain ⟨C0, hC0, hb⟩ := hbig
      have h1 : (if 3 ≤ C0.card then 3 else 0) ≤ ∑ C ∈ parts, (if 3 ≤ C.card then 3 else 0) :=
        Finset.single_le_sum (f := fun C : Finset V => if 3 ≤ C.card then 3 else 0)
          (fun _ _ => Nat.zero_le _) hC0
      have h2 : 1 ≤ parts.card := Finset.card_pos.mpr ⟨C0, hC0⟩
      rw [if_pos hb] at h1
      omega
    · push Not at hbig
      have : ∑ C ∈ parts, C.card ≤ ∑ C ∈ parts, 2 :=
        Finset.sum_le_sum (fun C hC => by have := hbig C hC; omega)
      rw [hcard, Finset.sum_const, smul_eq_mul] at this
      omega
  rw [hEdgeSum]
  change ∑ C ∈ parts, e C ≤ _
  omega
