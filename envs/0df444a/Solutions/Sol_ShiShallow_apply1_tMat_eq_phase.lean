-- Prove2me | solution 1 for ShiShallow.apply1_tMat_eq_phase
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T04:24:03.537733+00:00
-- url     : https://prove2.me/submissions/aaafa0a3-3da6-48d2-be1a-0c4eb9bc0659

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

theorem solution {n : ℕ} (i : Fin n) (ψ : ShiShallow.QState n) :
    ShiShallow.apply1 ShiShallow.tMat i ψ =
      fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  funext x
  unfold ShiShallow.apply1
  rw [Fintype.sum_bool]
  cases hx : x i with
  | false =>
      have hu : Function.update x i false = x := by
        rw [← hx]; exact Function.update_eq_self i x
      rw [hu]
      simp [ShiShallow.tMat, Matrix.of_apply]
  | true =>
      have hu : Function.update x i true = x := by
        rw [← hx]; exact Function.update_eq_self i x
      rw [hu]
      simp [ShiShallow.tMat, Matrix.of_apply]
