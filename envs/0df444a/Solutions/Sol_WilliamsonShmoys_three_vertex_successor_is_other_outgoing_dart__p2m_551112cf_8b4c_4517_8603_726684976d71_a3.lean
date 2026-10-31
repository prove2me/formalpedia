-- Prove2me | solution 1 for WilliamsonShmoys.three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:39:33.542519+00:00
-- url     : https://prove2.me/submissions/171c16f9-5d12-4c84-b0a5-dc74b4465070

import Theorems.Thm_WilliamsonShmoys_three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a4

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f)) :
    let succ : H.Dart → H.Dart :=
      fun a => dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)
    ∀ d : H.Dart, (succ d).fst = d.fst ∧ succ d ≠ d :=
  WilliamsonShmoys.three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a4 H F corner dart hTail hHead hInjective
