-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_reachable_class_connected__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:47:37.953187+00:00
-- url     : https://prove2.me/submissions/bd79f279-e817-43ed-b947-a8891d4d4125

import Mathlib
open Classical
open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (v : V) : (M.induce ((Finset.univ.filter (fun w => M.Reachable v w) : Finset V) : Set V)).Connected := by
  classical
  let s : Set V := (Finset.univ.filter (fun w => M.Reachable v w) : Finset V)
  change (M.induce s).Connected
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have hsupport : ∀ {a b : V} (p : M.Walk a b), M.Reachable v a → ∀ x ∈ p.support, M.Reachable v x := by
    intro a b p
    induction p with
    | nil =>
        intro ha x hx
        simp only [Walk.support_nil, List.mem_singleton] at hx
        subst x
        exact ha
    | @cons a b c hab p ih =>
        intro ha x hx
        simp only [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact ih (ha.trans hab.reachable) x hx
  refine ⟨⟨v, ?_⟩, ?_⟩
  · simp [s]
  · intro w
    have hw : M.Reachable v w.val := by simpa [s] using w.property
    obtain ⟨p⟩ := hw
    exact ⟨p.induce s (by
      intro x hx
      simpa [s] using hsupport p SimpleGraph.Reachable.rfl x hx)⟩