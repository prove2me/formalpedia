-- Prove2me | solution 1 for PermanentRollout.homogeneous_fin_one_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/6549ca02-d362-443d-8353-8c51095bc7eb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneous_fin_one_eq_C_mul_X_pow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution
    {f : MvPolynomial (Fin 1) ℂ} {e : ℕ}
    (hf : f.IsHomogeneous e) (u : Fin 1 → ℂ) :
    MvPolynomial.eval u f =
      u 0 ^ e * MvPolynomial.eval (fun _ : Fin 1 => 1) f := by
  rw [homogeneous_fin_one_eq_C_mul_X_pow hf]
  simp [mul_comm]
end PermanentRollout
