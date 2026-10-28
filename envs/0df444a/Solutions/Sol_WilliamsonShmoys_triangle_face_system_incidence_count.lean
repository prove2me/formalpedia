-- Prove2me | solution 1 for WilliamsonShmoys.triangle_face_system_incidence_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:45:20.537097+00:00
-- url     : https://prove2.me/submissions/9daec98b-4029-4951-ad79-4abff5a16240

import Mathlib


theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    (faces : Multiset (Finset V))
    (hcard : ∀ f, f ∈ faces → f.card = 3)
    (hadj : ∀ f, f ∈ faces → ∀ u, u ∈ f → ∀ v, v ∈ f →
      u ≠ v → H.Adj u v)
    (hincidence : ∀ u v, H.Adj u v →
      (faces.filter (fun f => u ∈ f ∧ v ∈ f)).card = 2) :
    3 * faces.card = 2 * H.edgeSet.ncard := by
  classical
  set E := H.edgeFinset with hEdef
  have hswap : ∀ s : Multiset (Finset V),
      ∑ e ∈ E, s.countP (fun f => ∀ x ∈ e, x ∈ f) =
        (s.map (fun f => (E.filter (fun e => ∀ x ∈ e, x ∈ f)).card)).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ← ih]
      simp only [Multiset.countP_cons]
      rw [Finset.sum_add_distrib, Finset.card_filter, add_comm]
  have hE2 : ∀ e ∈ E, faces.countP (fun f => ∀ x ∈ e, x ∈ f) = 2 := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [hEdef, SimpleGraph.mem_edgeFinset] at he
      rw [Multiset.countP_eq_card_filter, ← hincidence u v he]
      congr 1
      apply Multiset.filter_congr
      intro f _
      simp [Sym2.mem_iff]
  have hF3 : ∀ f ∈ faces, (E.filter (fun e => ∀ x ∈ e, x ∈ f)).card = 3 := by
    intro f hf
    have hA := hadj f hf
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 (hcard f hf)
    have hset : E.filter (fun e => ∀ w ∈ e, w ∈ ({x, y, z} : Finset V)) =
        {s(x, y), s(x, z), s(y, z)} := by
      ext e
      induction e using Sym2.ind with
      | h a b =>
        simp only [hEdef, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff, Sym2.eq_iff]
        constructor
        · rintro ⟨hab, h⟩
          have ha := h a (Or.inl rfl)
          have hb := h b (Or.inr rfl)
          have hne := hab.ne
          rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
        · intro h
          have hmem : (a = x ∨ a = y ∨ a = z) ∧ (b = x ∨ b = y ∨ b = z) ∧ a ≠ b := by
            rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
              (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp_all [eq_comm]
          refine ⟨hA a (by simp [hmem.1]) b (by simp [hmem.2.1]) hmem.2.2, ?_⟩
          rintro w (rfl | rfl)
          · exact hmem.1
          · exact hmem.2.1
    rw [hset, Finset.card_eq_three]
    refine ⟨s(x, y), s(x, z), s(y, z), ?_, ?_, ?_, rfl⟩ <;> simp [Sym2.eq_iff, *, Ne.symm hxy,
      Ne.symm hxz, Ne.symm hyz]
  have hL : ∑ e ∈ E, faces.countP (fun f => ∀ x ∈ e, x ∈ f) = 2 * E.card := by
    rw [Finset.sum_congr rfl hE2]; simp [mul_comm]
  have hR : (faces.map (fun f => (E.filter (fun e => ∀ x ∈ e, x ∈ f)).card)).sum =
      3 * faces.card := by
    rw [Multiset.map_congr rfl hF3]; simp [mul_comm]
  have hcard' : E.card = H.edgeSet.ncard := by
    rw [hEdef, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  have := hswap faces
  rw [hL, hR, hcard'] at this
  omega
