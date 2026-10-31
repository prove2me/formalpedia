-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertex_partition__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:40.54724+00:00
-- url     : https://prove2.me/submissions/93e628c0-a349-4103-9d9b-985accc0473f

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDisc : ¬ M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      (∀ ⦃u v : V⦄, u ∈ A → v ∉ A → ¬ M.Adj u v) := by
  have hcard : 0 < Fintype.card V := by omega
  have hnon : Nonempty V := Fintype.card_pos_iff.mp hcard
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hDisc
  push_neg at hDisc
  obtain ⟨x⟩ := hnon
  obtain ⟨y, hy⟩ := hDisc x
  let A : Set V := {z | M.Reachable x z}
  refine ⟨A, ?_, ?_, ?_⟩
  · exact ⟨x, by simp [A]⟩
  · exact ⟨y, by simpa [A] using hy⟩
  · intro u v hu hv hadj
    apply hv
    exact hu.trans hadj.reachable