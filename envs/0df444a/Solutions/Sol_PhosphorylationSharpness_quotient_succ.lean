-- Prove2me | solution 1 for PhosphorylationSharpness.quotient_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:45.301454+00:00
-- url     : https://prove2.me/submissions/dd7a6fd6-d096-4a9a-9b2b-dbe64f6d1bd5

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution (p q : ℝ[X]) {r : ℝ} (hr : r ≠ 0) (i : ℕ) :
    (quotient p q r).coeff (i+1) = p.eval r*q.coeff (i+1) +
      ((quotient p q r).coeff i-q.eval r*p.coeff i)/r := by
  have h := coeff_divByMonic_X_sub_C_rec (conversionNumerator p q r) r i
  change (quotient p q r).coeff i = _ + r*(quotient p q r).coeff (i+1) at h
  simp only [conversionNumerator, coeff_sub, coeff_C_mul, coeff_X_mul] at h
  field_simp
  nlinarith [h]
end PhosphorylationSharpness
