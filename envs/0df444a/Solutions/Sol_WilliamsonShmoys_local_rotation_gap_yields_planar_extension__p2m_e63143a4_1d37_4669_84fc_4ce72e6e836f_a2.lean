-- Prove2me | solution 1 for WilliamsonShmoys.local_rotation_gap_yields_planar_extension__p2m_e63143a4_1d37_4669_84fc_4ce72e6e836f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:06:17.291495+00:00
-- url     : https://prove2.me/submissions/0e9df825-e263-4b57-9921-38903a22d450
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_noncomplete_strict_extension__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
import Theorems.Thm_WilliamsonShmoys_complete_planar_triangular_map_rotation_transitive__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f))
    (hCovered : ∀ v, ∃ f i, corner f i = v)
    (d e : H.Dart)
    (hde : d.fst = e.fst)
    (hgap :
      ¬ ∃ k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ H := by
  by_cases hcomplete : ∀ u v : V, u ≠ v → H.Adj u v
  · have hrotation :=
      WilliamsonShmoys.complete_planar_triangular_map_rotation_transitive__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
        H hH hV F corner dart hTail hHead hInjective hCovered hcomplete
    exact False.elim (hgap (hrotation d e hde))
  · exact
      WilliamsonShmoys.planar_graph_noncomplete_strict_extension__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
        H hH hV hcomplete