-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_boundary_certificate_for_edge_bound_4091134b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:58:32.919431+00:00
-- url     : https://prove2.me/submissions/048f5e8e-fd9d-4d0e-a91c-06bccb71dbdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simple_connected_planar_edge_range__p2m_a5ca72a9_ecf9_4fb7_a47f_154e4f49a23b_a5

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hconn : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ lengths : List ℕ,
      (∀ k ∈ lengths, 3 ≤ k) ∧
      lengths.sum = 2 * T.edgeSet.ncard ∧
      Fintype.card V + lengths.length = T.edgeSet.ncard + 2 := by
  let n := Fintype.card V
  let m := T.edgeSet.ncard
  have hrange :=
    WilliamsonShmoys.simple_connected_planar_edge_range__p2m_a5ca72a9_ecf9_4fb7_a47f_154e4f49a23b_a5
      T hdraw hconn hV
  have hm_upper : m + 6 ≤ 3 * n := hrange.1
  have hn_lower : n ≤ m + 1 := hrange.2
  let f := m + 2 - n
  have hf : 1 ≤ f := by
    dsimp [f]
    omega
  have hthree : 3 * f ≤ 2 * m := by
    dsimp [f]
    omega
  let lengths : List ℕ := (3 + (2 * m - 3 * f)) :: List.replicate (f - 1) 3
  refine ⟨lengths, ?_, ?_, ?_⟩
  · intro k hk
    simp [lengths] at hk
    rcases hk with hk | hk <;> omega
  · have hsum : lengths.sum = 2 * m := by
      simp [lengths]
      omega
    simpa [n, m] using hsum
  · have hlen : lengths.length = f := by
      simp [lengths]
      omega
    dsimp [n, m, f] at hlen ⊢
    omega