-- Prove2me | solution 1 for UpperTheory.measurable_matrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:43.465168+00:00
-- url     : https://prove2.me/submissions/666b0dbe-6314-41b8-9e77-ec77c7850884

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MeasurableMatrixInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ n : ℕ, Measurable (fun x : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of x : Matrix (Fin n) (Fin n) ℂ)⁻¹) : Fin n → Fin n → ℂ)) := by
  intro n
  have hc : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_id
  have hdet : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).det) := hc.matrix_det.measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have hadj : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).adjugate i j) :=
    (hc.matrix_adjugate.matrix_elem i j).measurable
  have h := hdet.inv.mul hadj
  convert h using 1
  funext x
  simp only [Matrix.of_symm_apply, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Pi.mul_apply, Pi.inv_apply]
end UpperTheory
