-- Prove2me | solution 1 for PhosphorylationSharpness.quotient_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:41.483219+00:00
-- url     : https://prove2.me/submissions/2f273a86-582b-44d8-8207-ea9987e7e2eb

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_quotient_identity

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution (p q : ℝ[X]) {r : ℝ} (hr : r ≠ 0) :
    (quotient p q r).coeff 0 = p.eval r*q.coeff 0 := by
  have h := congrArg (fun f : ℝ[X] => f.coeff 0) (quotient_identity p q r)
  simp only [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul,
    conversionNumerator] at h
  have hh : r*((quotient p q r).coeff 0-p.eval r*q.coeff 0)=0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hr)
end PhosphorylationSharpness
