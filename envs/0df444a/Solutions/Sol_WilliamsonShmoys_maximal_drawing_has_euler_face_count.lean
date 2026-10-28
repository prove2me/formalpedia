-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_has_euler_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:08:51.983279+00:00
-- url     : https://prove2.me/submissions/73995e26-95c3-4d66-8c2b-cbcffa1300c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_euler_identity_from_maximality_42d00589

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hE : 3 * Fintype.card V = K.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_drawing_euler_identity_from_maximality_42d00589
      K hK hmax hCard
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  omega