-- Prove2me | solution 1 for PHIP1887.diagonal_first_euler
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:47:56.854551+00:00
-- url     : https://prove2.me/submissions/79843bf3-c2cd-4d0f-b21d-6929a0b86f24

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem solution (k : ℕ) (z : ℂ) :
    EulerY (fun w => (w*(1-w))^(k+1)) z =
      (k+1 : ℂ)*(z*(1-z))^(k+1)*(1-2*z) := by
  have hp := ((hasDerivAt_id z).mul
    ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z))).pow (k+1)
  change HasDerivAt (fun w : ℂ => (w*(1-w))^(k+1)) _ z at hp
  unfold EulerY
  rw [hp.deriv]
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  ring
