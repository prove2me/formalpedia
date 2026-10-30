-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_vertex_rotation__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:18.87722+00:00
-- url     : https://prove2.me/submissions/691319a6-084b-4bc9-9435-10b5036a10f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_local_rotation_gap_yields_planar_extension__p2m_e63143a4_1d37_4669_84fc_4ce72e6e836f_a2
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = H)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f))
    (hCovered : ∀ v, ∃ f i, corner f i = v) :
    ∀ d e : H.Dart, d.fst = e.fst →
      ∃ k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e := by
  intro d e hde
  by_contra hnot
  have hgap :
      ¬ ∃ k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e := by
    simpa using hnot
  obtain ⟨M, hHM, hMPlanar, hMNe⟩ :=
    WilliamsonShmoys.local_rotation_gap_yields_planar_extension__p2m_e63143a4_1d37_4669_84fc_4ce72e6e836f_a2
      H hH hV F corner dart hTail hHead hInjective hCovered d e hde hgap
  exact hMNe (hMax M hHM hMPlanar)