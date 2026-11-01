-- Prove2me | solution 4 for WilliamsonShmoys.four_vertex_triangular_rotation_transitive__p2m_a3a0a250_04a2_4577_b872_e6afd6b9d768_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:14.178367+00:00
-- url     : https://prove2.me/submissions/47a62622-56f6-4f72-b84d-a1ea37acb2a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Theorems.Thm_WilliamsonShmoys_localSuccessor_tail__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
import Theorems.Thm_WilliamsonShmoys_localSuccessor_injective__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
import Theorems.Thm_WilliamsonShmoys_four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
import Theorems.Thm_WilliamsonShmoys_localSuccessor_ne_self_structured__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a11
import Theorems.Thm_finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : Fintype.card V = 4)
    (F : Type) [Fintype F]
    (corner : F -> Fin 3 -> V)
    (dart : Equiv (Prod F (Fin 3)) H.Dart)
    (hTail : forall f i, (dart (f, i)).fst = corner f i)
    (hHead : forall f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : forall f, Function.Injective (corner f))
    (hCovered : forall v, exists f i, corner f i = v)
    (hcomplete : forall u v : V, Not (u = v) -> H.Adj u v) :
    forall d e : H.Dart, d.fst = e.fst ->
      exists k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e := by
  classical
  intro d e hde
  let succ : H.Dart -> H.Dart := fun a =>
    dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)
  have hpres : forall a : H.Dart, a.fst = d.fst -> (succ a).fst = d.fst := by
    intro a ha
    rw [WilliamsonShmoys.localSuccessor_tail__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
      corner dart hTail hHead a]
    exact ha
  have hinj : Function.Injective succ :=
    WilliamsonShmoys.localSuccessor_injective__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8 dart
  have hfixed : forall a : H.Dart, Not (succ a = a) := by
    intro a
    exact WilliamsonShmoys.localSuccessor_ne_self_structured__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a11
      corner dart hTail hHead hInjective a
  exact finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
    succ (fun a : H.Dart => a.fst = d.fst)
    (WilliamsonShmoys.four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
      H hV (fun u v huv => hcomplete u v huv) d.fst)
    hpres hinj hfixed d e rfl hde.symm
