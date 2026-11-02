-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_connected_extension_of_one_edge__p2m_aa9f8502_788d_4376_8cf6_48061960ef49_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:40:19.98911+00:00
-- url     : https://prove2.me/submissions/7612c0df-e645-44bc-bf2e-d36f5ef4d0ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_bounded_progress_has_terminal_path__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
import Theorems.Thm_WilliamsonShmoys_finite_graph_edge_rank_progress__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
import Theorems.Thm_WilliamsonShmoys_finite_graph_edge_rank_bound__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hP : P G)
    (hstep : ∀ G : SimpleGraph V,
      P G → ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          G ≤ H ∧
          H.edgeSet = G.edgeSet ∪ {Sym2.mk u v} ∧
          P H) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H := by
  classical
  let State := {A : SimpleGraph V // P A}
  let step : State → State → Prop := fun A B =>
    ∃ u v : V, ¬ A.val.Reachable u v ∧ A.val ≤ B.val ∧
      B.val.edgeSet = A.val.edgeSet ∪ {Sym2.mk u v}
  let terminal : State → Prop := fun A => A.val.Connected
  let rank : State → Nat := fun A => A.val.edgeSet.ncard
  have hbound : ∀ A : State, rank A ≤ Fintype.card (Sym2 V) := by
    intro A
    exact WilliamsonShmoys.finite_graph_edge_rank_bound__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2 A.val
  have hprogress : ∀ A : State,
      ¬ terminal A → ∃ B, step A B ∧ rank A < rank B := by
    intro A hA
    obtain ⟨u, v, huv, H, hle, hedges, hPH⟩ := hstep A.val A.property hA
    let B : State := ⟨H, hPH⟩
    refine ⟨B, ⟨u, v, huv, hle, hedges⟩, ?_⟩
    exact (WilliamsonShmoys.finite_graph_edge_rank_progress__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2 A.val H u v huv hedges)
  obtain ⟨H, hpath, hterminal⟩ :=
    WilliamsonShmoys.bounded_progress_has_terminal_path__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
      (Fintype.card (Sym2 V)) rank step terminal hbound hprogress ⟨G, hP⟩
  have hinclusion : ∀ {A : State}, Relation.ReflTransGen step ⟨G, hP⟩ A → G ≤ A.val := by
    intro A h
    induction h with
    | refl => exact le_rfl
    | tail hpath hAB ih =>
        rcases hAB with ⟨u, v, huv, hle, hedges⟩
        exact ih.trans hle
  exact ⟨H.val, hinclusion hpath, hterminal, H.property⟩