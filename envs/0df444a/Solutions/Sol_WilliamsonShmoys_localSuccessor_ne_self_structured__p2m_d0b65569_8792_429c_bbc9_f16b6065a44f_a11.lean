-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_ne_self_structured__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a11
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:37.669542+00:00
-- url     : https://prove2.me/submissions/097aa8fc-b10b-4e11-ab9b-dd2927fef11a

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] {F : Type} [Fintype F]
    {H : SimpleGraph V}
    (corner : F -> Fin 3 -> V)
    (dart : Equiv (Prod F (Fin 3)) H.Dart)
    (hTail : forall f i, (dart (f, i)).fst = corner f i)
    (hHead : forall f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : forall f, Function.Injective (corner f))
    (a : H.Dart) :
    Not (dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1) = a) := by
  intro hfixed
  cases hq : dart.symm a.symm with
  | mk f i =>
    have hrev : dart (f, i) = a.symm := by
      have h := Equiv.apply_symm_apply dart a.symm
      simpa [hq] using h
    have hnext : dart (f, i + 1) = a := by
      simpa [hq] using hfixed
    have hcorner1 : corner f i = a.snd := by
      calc
        corner f i = (dart (f, i)).fst := (hTail f i).symm
        _ = a.snd := by rw [hrev]; simp
    have hcorner2 : corner f ((i + 1) + 1) = a.snd := by
      calc
        corner f ((i + 1) + 1) = (dart (f, i + 1)).snd := (hHead f (i + 1)).symm
        _ = a.snd := by rw [hnext]
    have hidx : Not (i = (i + 1) + 1) := by
      fin_cases i <;> decide
    exact hidx (hInjective f (hcorner1.trans hcorner2.symm))