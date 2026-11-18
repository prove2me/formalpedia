-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-17T09:38:05.101004+00:00
-- url     : https://prove2.me/submissions/243e62c7-15e3-4c0e-8398-60bd2cae2ece

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (dart : (F × Fin 3) ≃ H.Dart) (a : H.Dart),
    (fun a : H.Dart =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) a ≠ a) := by
  intro Hall
  classical
  let H : SimpleGraph (Fin 3) := ⊤
  have hcard : Fintype.card (Fin 2 × Fin 3) = Fintype.card H.Dart := by
    rw [SimpleGraph.dart_card_eq_twice_card_edges, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp
  let e0 : (Fin 2 × Fin 3) ≃ H.Dart := Fintype.equivOfCardEq hcard
  let p : Fin 2 × Fin 3 := (0, 0)
  let q : Fin 2 × Fin 3 := (0, 1)
  let d : H.Dart := e0 p
  let dart : (Fin 2 × Fin 3) ≃ H.Dart := e0.trans (Equiv.swap (e0 q) d.symm)
  have hpq : p ≠ q := by decide
  have hd : d ≠ d.symm := (SimpleGraph.Dart.symm_ne d).symm
  have hdp : dart p = d := by
    show Equiv.swap (e0 q) d.symm (e0 p) = d
    rw [Equiv.swap_apply_of_ne_of_ne (fun h => hpq (e0.injective h)) hd]
  have hdq : dart q = d.symm := by
    show Equiv.swap (e0 q) d.symm (e0 q) = d.symm
    rw [Equiv.swap_apply_left]
  have key := @Hall (Fin 3) _ (Fin 2) _ H dart d.symm
  apply key
  simp only [SimpleGraph.Dart.symm_symm]
  have : dart.symm d = p := by rw [← hdp, Equiv.symm_apply_apply]
  rw [this]
  exact hdq
