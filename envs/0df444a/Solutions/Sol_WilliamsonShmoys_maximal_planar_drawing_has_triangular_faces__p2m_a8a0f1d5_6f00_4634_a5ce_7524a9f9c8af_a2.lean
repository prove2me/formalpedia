-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangular_faces__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:48:12.6347+00:00
-- url     : https://prove2.me/submissions/957f1b62-3f2d-418f-8605-632e5f8fbed2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_system__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_faces_are_triangles__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (faceInst : Fintype F)
      (boundary : F → Finset (Sym2 V)),
      (∀ f, (boundary f).card = 3) ∧
      (∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet) ∧
      (∀ e ∈ L.edgeSet,
        ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2) := by
  obtain ⟨F, faceInst, boundary, hsize, hmem, hinc⟩ :=
    WilliamsonShmoys.maximal_planar_face_system__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
      L hL hMax hCard
  have htri :=
    WilliamsonShmoys.maximal_planar_faces_are_triangles__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
      L hL hMax F faceInst boundary hsize hmem hinc hCard
  exact ⟨F, faceInst, boundary, htri, hmem, hinc⟩