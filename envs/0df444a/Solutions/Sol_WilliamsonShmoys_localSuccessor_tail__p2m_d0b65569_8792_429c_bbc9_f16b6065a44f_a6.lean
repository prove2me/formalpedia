-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_tail__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:27.552949+00:00
-- url     : https://prove2.me/submissions/83b66dbd-e171-4073-8aeb-937459b3fd8c

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (corner : F -> Fin 3 -> V) (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (a : H.Dart) :
    (dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)).fst = a.fst := by
  let p : F × Fin 3 := dart.symm a.symm
  have hp : dart p = a.symm := Equiv.apply_symm_apply dart a.symm
  rw [hTail p.1 (p.2 + 1)]
  have hh := hHead p.1 p.2
  rw [hp] at hh
  simpa using hh.symm