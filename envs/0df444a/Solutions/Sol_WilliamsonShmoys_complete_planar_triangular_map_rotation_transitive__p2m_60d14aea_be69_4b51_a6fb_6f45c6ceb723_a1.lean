-- Prove2me | solution 1 for WilliamsonShmoys.complete_planar_triangular_map_rotation_transitive__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:09:17.201275+00:00
-- url     : https://prove2.me/submissions/c51b69fd-2dcf-4ae6-ad72-ec6fb3cd4a63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_card_eq_three_of_planar_complete__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
import Theorems.Thm_WilliamsonShmoys_three_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1

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
  have hcard : Fintype.card V = 3 :=
    WilliamsonShmoys.card_eq_three_of_planar_complete__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
      H hH hV hcomplete
  exact WilliamsonShmoys.three_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
    H hcard F corner dart hTail hHead hInjective hCovered hcomplete