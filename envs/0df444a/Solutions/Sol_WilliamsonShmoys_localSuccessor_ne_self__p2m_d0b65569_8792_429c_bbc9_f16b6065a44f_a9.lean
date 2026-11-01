-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:46.503822+00:00
-- url     : https://prove2.me/submissions/df15d647-86e5-4f13-b511-21573143a5c5

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
        (dart : Equiv (Prod F (Fin 3)) H.Dart) (a : H.Dart),
        Not ((fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) a = a)) := by
  classical
  intro h
  let H : SimpleGraph (Fin 3) := ⊤
  have hcard : Fintype.card (Fin 2 × Fin 3) = Fintype.card H.Dart := by
    decide
  let e : (Fin 2 × Fin 3) ≃ H.Dart := Fintype.equivOfCardEq hcard
  let s : Fin 2 × Fin 3 := (0, 2)
  let t : Fin 2 × Fin 3 := (0, 1)
  let u : H.Dart := e s
  let v : H.Dart := e t
  have huv : u ≠ v := by
    intro heq
    have hst : s = t := e.injective heq
    have hidx : (2 : Fin 3) = 1 := congrArg Prod.snd hst
    exact (by decide : (2 : Fin 3) ≠ 1) hidx
  have hvs : v ≠ v.symm := by
    intro heq
    exact (SimpleGraph.Dart.symm_ne v) heq.symm
  let p : Equiv H.Dart H.Dart :=
    if hv : v = u.symm then Equiv.refl _ else Equiv.swap u v.symm
  have hp : p v = (p u).symm := by
    by_cases hv : v = u.symm
    · simp [p, hv]
    · have hvu : v ≠ u := huv.symm
      have huv' : u ≠ v.symm := by
        intro heq
        apply hv
        simpa using congrArg SimpleGraph.Dart.symm heq.symm
      simp [p, hv, Equiv.swap_apply_def, hvu, hvs, huv']
  let d : Equiv (Fin 2 × Fin 3) H.Dart := e.trans p
  have hpair : d t = (d s).symm := by
    change p v = (p u).symm
    exact hp
  have hpre : d.symm (d s).symm = t := by
    rw [← hpair]
    exact d.symm_apply_apply t
  have heq :
      (fun a : H.Dart =>
        d ((d.symm a.symm).1, (d.symm a.symm).2 + 1)) (d s) = d s := by
    change d ((d.symm (d s).symm).1, (d.symm (d s).symm).2 + 1) = d s
    rw [hpre]
    simp [s, t]
  have hn := h (V := Fin 3) (F := Fin 2) (H := H) d (d s)
  exact hn heq