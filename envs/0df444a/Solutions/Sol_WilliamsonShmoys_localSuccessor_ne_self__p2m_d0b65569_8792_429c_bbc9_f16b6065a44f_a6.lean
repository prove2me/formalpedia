-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:00.18636+00:00
-- url     : https://prove2.me/submissions/93ab3a5b-b661-4134-9b98-cb9fb084c5c6

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
        (dart : (F × Fin 3) ≃ H.Dart) (a : H.Dart),
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) a ≠ a) := by
  intro h
  let H : SimpleGraph (Fin 3) := ⊤
  let D : (x y : Fin 3) → x ≠ y → H.Dart := fun x y hxy =>
    ⟨(x, y), by change x ≠ y; exact hxy⟩
  let f : Fin 2 × Fin 3 → H.Dart := fun p =>
    match p.1.val, p.2.val with
    | 0, 0 => D 1 0 (by decide)
    | 0, 1 => D 0 1 (by decide)
    | 0, 2 => D 0 2 (by decide)
    | 1, 0 => D 1 2 (by decide)
    | 1, 1 => D 2 1 (by decide)
    | 1, 2 => D 2 0 (by decide)
    | _, _ => D 0 1 (by decide)
  have hf : Function.Bijective f := by
    constructor <;> decide
  let e : (Fin 2 × Fin 3) ≃ H.Dart := Equiv.ofBijective f hf
  let a : H.Dart := e (0, 1)
  have hrev : a.symm = e (0, 0) := by
    rfl
  have hdecode : e.symm a.symm = (0, 0) := by
    rw [hrev]
    simp
  have hfix :
      (fun a : H.Dart =>
        e ((e.symm a.symm).1, (e.symm a.symm).2 + 1)) a = a := by
    change e ((e.symm a.symm).1, (e.symm a.symm).2 + 1) = a
    rw [hdecode]
    rfl
  have hne := h (V := Fin 3) (F := Fin 2) (H := H) e a
  exact hne hfix