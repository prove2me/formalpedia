-- Prove2me | solution 1 for WilliamsonShmoys.three_or_four_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:54.17067+00:00
-- url     : https://prove2.me/submissions/527c46ec-bcc0-4054-a706-a8098523bcf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Theorems.Thm_WilliamsonShmoys_three_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
import Theorems.Thm_WilliamsonShmoys_four_vertex_triangular_rotation_transitive__p2m_a3a0a250_04a2_4577_b872_e6afd6b9d768_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hVlo : 3 ≤ Fintype.card V)
    (hVhi : Fintype.card V ≤ 4)
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
  by_cases h3 : Fintype.card V = 3
  · exact WilliamsonShmoys.three_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
      H h3 F corner dart hTail hHead hInjective hCovered hcomplete
  · have h4 : Fintype.card V = 4 := by omega
    exact WilliamsonShmoys.four_vertex_triangular_rotation_transitive__p2m_a3a0a250_04a2_4577_b872_e6afd6b9d768_a1
      H h4 F corner dart hTail hHead hInjective hCovered hcomplete