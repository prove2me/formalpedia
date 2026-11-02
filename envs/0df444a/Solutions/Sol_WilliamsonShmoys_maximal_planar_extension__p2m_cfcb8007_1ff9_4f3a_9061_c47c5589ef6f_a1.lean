-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T19:16:50.798879+00:00
-- url     : https://prove2.me/submissions/e3fdcfe4-1b25-4a0f-8f98-29f2df87b83d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      HasPlanarDrawingOn M ∧
      (∀ u v, L.Adj u v → M.Adj u v) ∧
      (∀ N : SimpleGraph V, HasPlanarDrawingOn N →
        (∀ u v, M.Adj u v → N.Adj u v) →
        ∀ u v, N.Adj u v → M.Adj u v) := by
  classical
  let P : SimpleGraph V → Prop := fun G =>
    HasPlanarDrawingOn G ∧ ∀ u v, L.Adj u v → G.Adj u v
  have hPL : P L := ⟨hL, fun _ _ huv => huv⟩
  obtain ⟨M, hLM, hMax⟩ :=
    ({G : SimpleGraph V | P G}.toFinite).exists_le_maximal hPL
  refine ⟨M, hMax.prop.1, ?_, ?_⟩
  · intro u v huv
    exact hLM huv
  · intro N hN hMN u v huv
    have hPN : P N :=
      ⟨hN, fun x y hxy => hMN x y (hLM hxy)⟩
    have hMNle : M ≤ N := by
      intro x y hxy
      exact hMN x y hxy
    have hEq : M = N := hMax.eq_of_le hPN hMNle
    rw [hEq]
    exact huv
