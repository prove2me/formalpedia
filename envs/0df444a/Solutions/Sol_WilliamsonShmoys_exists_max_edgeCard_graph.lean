-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_edgeCard_graph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:18:47.808978+00:00
-- url     : https://prove2.me/submissions/04309470-2f93-459f-b4a0-71ecb58bfdba

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (edgeFinite : ∀ G : SimpleGraph V, Fintype G.edgeSet)
    (P : SimpleGraph V → Prop)
    (hP : ∃ G : SimpleGraph V, P G) :
    ∃ M : SimpleGraph V,
      P M ∧ ∀ N : SimpleGraph V, P N → N.edgeFinset.card ≤ M.edgeFinset.card := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  letI : Fintype {G : SimpleGraph V // P G} :=
    Fintype.ofFinite {G : SimpleGraph V // P G}
  obtain ⟨G₀, hG₀⟩ := hP
  let edgeCount : {G : SimpleGraph V // P G} → Nat := fun G => by
    letI : Fintype G.1.edgeSet := edgeFinite G.1
    exact G.1.edgeFinset.card
  obtain ⟨M, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ edgeCount
      (Finset.univ_nonempty_iff.mpr ⟨⟨G₀, hG₀⟩⟩)
  refine ⟨M.1, M.2, ?_⟩
  intro N hN
  let N' : {G : SimpleGraph V // P G} := ⟨N, hN⟩
  have hbound := hmax N' (Finset.mem_univ N')
  letI : Fintype N.edgeSet := edgeFinite N
  letI : Fintype M.1.edgeSet := edgeFinite M.1
  simpa [edgeCount] using hbound
