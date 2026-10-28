-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:29:18.842176+00:00
-- url     : https://prove2.me/submissions/085c59ff-cd1e-45f9-b2bd-dc00cdd07919
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_planar_edge_upper
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_maximal_edge_lower

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hupper := WilliamsonShmoys.maximal_planar_face_count_planar_edge_upper K hV hK
  have hlower := WilliamsonShmoys.maximal_planar_face_count_maximal_edge_lower K hV hK hmax
  have he : K.edgeSet.ncard = 3 * Fintype.card V - 6 := Nat.le_antisymm hupper hlower
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega