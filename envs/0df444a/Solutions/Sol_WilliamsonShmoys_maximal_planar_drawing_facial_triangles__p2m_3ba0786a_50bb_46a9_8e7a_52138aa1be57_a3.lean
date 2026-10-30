-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_facial_triangles__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:23.808468+00:00
-- url     : https://prove2.me/submissions/11ee7000-eee2-4b3c-90d9-7418fcde2070
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_map__p2m_69f7c61b_c390_4365_9e4f_b0c1ff980885_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    ∃ (F : Type) (instF : Fintype F)
      (corner : F → Fin 3 → V)
      (dart : (F × Fin 3) ≃ H.Dart),
      (∀ f i, (dart (f, i)).fst = corner f i) ∧
      (∀ f i, (dart (f, i)).snd = corner f (i + 1)) ∧
      (∀ f, Function.Injective (corner f)) ∧
      (∀ v, ∃ f i, corner f i = v) := by
  obtain ⟨F, instF, ⟨M⟩⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangular_map__p2m_69f7c61b_c390_4365_9e4f_b0c1ff980885_a2
      H hH hV hMax
  letI : Fintype F := instF
  exact ⟨F, instF, M.corner, M.dart, M.dart_tail, M.dart_head,
    M.corners_distinct, M.vertex_covered⟩