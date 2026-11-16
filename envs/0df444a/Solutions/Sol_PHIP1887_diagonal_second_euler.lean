-- Prove2me | solution 1 for PHIP1887.diagonal_second_euler
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:53:58.355944+00:00
-- url     : https://prove2.me/submissions/8fd95ece-5796-41e2-8070-ed2e34208fbd

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_diagonal_first_euler
open MeasureTheory Set
open PHIP1887

theorem solution (k : ℕ) (z : ℂ) :
    EulerY (EulerY (fun w => (w*(1-w))^(k+1))) z =
      (k+1 : ℂ)^2*(z*(1-z))^(k+1) -
      2*(k+1 : ℂ)*(2*(k+1 : ℂ)+1)*(z*(1-z))^(k+2) := by
  have hf : EulerY (fun w : ℂ => (w*(1-w))^(k+1)) =
      (fun w => (k+1 : ℂ)*(w*(1-w))^(k+1)*(1-2*w)) := by
    funext w
    exact diagonal_first_euler k w
  have hp := ((hasDerivAt_id z).mul
    ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z))).pow (k+1)
  have ht := ((hasDerivAt_const z (k+1:ℂ)).mul hp).mul
    ((hasDerivAt_const z (1:ℂ)).sub
      ((hasDerivAt_const z (2:ℂ)).mul (hasDerivAt_id z)))
  change HasDerivAt (fun w : ℂ => (k+1 : ℂ)*(w*(1-w))^(k+1)*(1-2*w)) _ z at ht
  rw [hf]
  unfold EulerY
  rw [ht.deriv]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  ring
