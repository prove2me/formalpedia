-- Prove2me | solution 1 for WilliamsonShmoys.exists_disconnected_partition_nonempty__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:43.565049+00:00
-- url     : https://prove2.me/submissions/25c8a55a-25a2-407f-b9b1-4ddc2646c134

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdisc : ¬ M.Connected) :
    ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      (∀ ⦃u v : V⦄, u ∈ A → v ∈ Aᶜ → ¬ M.Adj u v) := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  letI : Nonempty V := hne
  obtain ⟨u⟩ := hne
  have hsep : ∃ v, ¬ M.Reachable u v := by
    by_contra h
    have hreach : ∀ v, M.Reachable u v := by
      intro v
      by_contra hv
      exact h ⟨v, hv⟩
    have hconn : M.Connected := ⟨fun a b => (hreach a).symm.trans (hreach b)⟩
    exact hdisc hconn
  obtain ⟨v, hv⟩ := hsep
  refine ⟨{x | M.Reachable u x}, ?_, ?_, ?_⟩
  · exact ⟨u, by simp⟩
  · exact ⟨v, by simpa using hv⟩
  · intro x y hx hy hadj
    exact hy (hx.trans hadj.reachable)