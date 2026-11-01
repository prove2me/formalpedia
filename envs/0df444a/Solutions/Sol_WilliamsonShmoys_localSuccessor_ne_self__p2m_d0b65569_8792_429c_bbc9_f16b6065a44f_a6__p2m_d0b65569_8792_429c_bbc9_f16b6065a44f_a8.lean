-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:26.216865+00:00
-- url     : https://prove2.me/submissions/cd68f1d9-5729-4da1-ac8d-a03fbdabb045

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
        (dart : Equiv (Prod F (Fin 3)) H.Dart) (a : H.Dart),
        Not ((fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) a = a)) := by
  intro htarget
  let V := Fin 3
  let H : SimpleGraph V := ⊤
  let F := Fin 2
  let d01 : H.Dart := ⟨(0, 1), by decide⟩
  let d10 : H.Dart := ⟨(1, 0), by decide⟩
  let d02 : H.Dart := ⟨(0, 2), by decide⟩
  let d20 : H.Dart := ⟨(2, 0), by decide⟩
  let d12 : H.Dart := ⟨(1, 2), by decide⟩
  let d21 : H.Dart := ⟨(2, 1), by decide⟩
  let f : F × Fin 3 → H.Dart := fun p =>
    if p.1 = (0 : Fin 2) then
      if p.2 = (0 : Fin 3) then d01 else if p.2 = 1 then d10 else d02
    else if p.2 = 0 then d20 else if p.2 = 1 then d12 else d21
  have hf : Function.Bijective f := by decide
  let e : Equiv (F × Fin 3) H.Dart := Equiv.ofBijective f hf
  let a : H.Dart := e (0, 1)
  have ha : a = d10 := by simp [a, e, f, d01, d10, d02, d20, d12, d21]
  have hrev : e.symm a.symm = (0, 0) := by
    apply e.injective
    simp [a, e, f, d01, d10, d02, d20, d12, d21]
  have hs : e ((e.symm a.symm).1, (e.symm a.symm).2 + 1) = a := by
    rw [hrev, ha]
    simp [e, f, d01, d10, d02, d20, d12, d21]
  exact (htarget (V := V) (F := F) (H := H) e a) hs