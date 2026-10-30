-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangular_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:10.828696+00:00
-- url     : https://prove2.me/submissions/6fc63cef-ad5e-4268-b3bb-7d9945accb35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_e85b752f_0f40_4cd5_9669_1350472cdb99_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    ∀ f : ℕ, H.edgeSet.ncard + 2 = Fintype.card V + f →
      3 * f = 2 * H.edgeSet.ncard := by
  intro f hf
  obtain ⟨g, hgEuler, hgIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_e85b752f_0f40_4cd5_9669_1350472cdb99_a1
      H hplanar hmax hV
  omega