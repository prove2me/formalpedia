-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_data__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:54:48.660538+00:00
-- url     : https://prove2.me/submissions/b86e6bb8-65b6-48f3-a37a-739c2285967c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_facial_triangles__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_vertex_rotation__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    ∃ (F : Type) (instF : Fintype F)
      (corner : F → Fin 3 → V)
      (dart : (F × Fin 3) ≃ H.Dart),
      (∀ f i, (dart (f, i)).fst = corner f i) ∧
      (∀ f i, (dart (f, i)).snd = corner f (i + 1)) ∧
      (∀ f, Function.Injective (corner f)) ∧
      (∀ v, ∃ f i, corner f i = v) ∧
      (∀ d e : H.Dart, d.fst = e.fst →
        ∃ k : Nat,
          (fun a : H.Dart =>
            dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e) := by
  obtain ⟨F, instF, corner, dart, hTail, hHead, hInjective, hCovered⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_facial_triangles__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
      H hH hV hMax
  letI : Fintype F := instF
  have hRotation :=
    WilliamsonShmoys.maximal_planar_drawing_vertex_rotation__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
      H hH hV hMax F corner dart hTail hHead hInjective hCovered
  exact ⟨F, instF, corner, dart, hTail, hHead, hInjective, hCovered, hRotation⟩