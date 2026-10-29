-- Prove2me | solution 1 for WilliamsonShmoys.finite_face_incidence_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:35.940128+00:00
-- url     : https://prove2.me/submissions/33e9abcf-61e6-4751-93fb-ecedfdf5d1c5

import Mathlib

theorem solution
    {E F : Type} [Fintype E] [Fintype F] [DecidableEq E]
    (edges : Set E) (boundary : F → Finset E)
    (hCard : ∀ f, (boundary f).card = 3)
    (hBoundary : ∀ f, ∀ e ∈ boundary f, e ∈ edges)
    (hIncidence : ∀ e ∈ edges,
      ((Finset.univ : Finset F).filter (fun f => e ∈ boundary f)).card = 2) :
    3 * Fintype.card F = 2 * edges.ncard := by
  classical
  have h1 : ∑ f, (boundary f).card = 3 * Fintype.card F := by
    simp [hCard, mul_comm]
  have h2 : ∀ f, (boundary f).card =
      ∑ e ∈ edges.toFinset, (if e ∈ boundary f then 1 else 0) := by
    intro f
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext e
    simp only [Finset.mem_filter, Set.mem_toFinset]
    exact ⟨fun h => ⟨hBoundary f e h, h⟩, fun h => h.2⟩
  have h3 : ∀ e ∈ edges.toFinset,
      ∑ f, (if e ∈ boundary f then 1 else 0) = 2 := by
    intro e he
    rw [Finset.sum_boole, Nat.cast_id]
    exact hIncidence e (Set.mem_toFinset.mp he)
  rw [← h1, Finset.sum_congr rfl (fun f _ => h2 f), Finset.sum_comm,
    Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card',
    mul_comm]
