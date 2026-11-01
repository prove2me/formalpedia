-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_injective__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:13.836218+00:00
-- url     : https://prove2.me/submissions/d504bebd-31e7-4312-a83d-a0046f90e32c

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (dart : Equiv (Prod F (Fin 3)) H.Dart) :
    Function.Injective (fun a : H.Dart =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) := by
  intro a b h
  have hp := dart.injective h
  have hfst := congrArg Prod.fst hp
  have hsnd := congrArg Prod.snd hp
  have hindex : (dart.symm a.symm).2 = (dart.symm b.symm).2 :=
    add_right_cancel hsnd
  have hpair : dart.symm a.symm = dart.symm b.symm := Prod.ext hfst hindex
  have hrev : a.symm = b.symm := by
    simpa using congrArg dart hpair
  have hab := congrArg (fun x : H.Dart => x.symm) hrev
  simpa only [SimpleGraph.Dart.symm_symm] using hab