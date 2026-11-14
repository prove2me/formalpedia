-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.cxWires_shared_target_commute
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:40:15.286392+00:00
-- url     : https://prove2.me/submissions/18b333c7-4efe-4aaf-a4cf-2da7b284f1b3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52
set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (a b t : V) (ha : a ≠ t) (hb : b ≠ t) :
    cxWires a t * cxWires b t = cxWires b t * cxWires a t := by
  ext y z
  simp only [cxWires, Matrix.mul_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hh : Function.update (Function.update z t (xor (z t) (z b))) t
      (xor ((Function.update z t (xor (z t) (z b))) t)
        ((Function.update z t (xor (z t) (z b))) a)) =
      Function.update (Function.update z t (xor (z t) (z a))) t
      (xor ((Function.update z t (xor (z t) (z a))) t)
        ((Function.update z t (xor (z t) (z a))) b)) := by
    funext i
    by_cases hi : i = t
    · subst i
      simp only [Function.update_self, Function.update_of_ne ha, Function.update_of_ne hb]
      cases z t <;> cases z a <;> cases z b <;> simp
    · simp [Function.update_of_ne hi]
  rw [hh]