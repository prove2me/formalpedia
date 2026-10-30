-- Prove2me | solution 2 for WilliamsonShmoys.complete_planar_triangular_map_rotation_transitive__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:57.970766+00:00
-- url     : https://prove2.me/submissions/7245f7ed-b041-4a64-8cbe-211d34954a86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_complete_card_le_four__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
import Theorems.Thm_WilliamsonShmoys_three_or_four_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2

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
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v) :
    ∀ d e : H.Dart, d.fst = e.fst →
      ∃ k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e := by
  have hVhi : Fintype.card V ≤ 4 :=
    WilliamsonShmoys.planar_complete_card_le_four__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
      H hH hcomplete
  exact WilliamsonShmoys.three_or_four_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
    H hV hVhi F corner dart hTail hHead hInjective hCovered hcomplete