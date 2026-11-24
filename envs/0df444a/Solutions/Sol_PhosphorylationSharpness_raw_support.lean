-- Prove2me | solution 1 for PhosphorylationSharpness.raw_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:43.454785+00:00
-- url     : https://prove2.me/submissions/ab2a3faf-5782-42ec-b712-f75b79651aaa

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_quotient_degree

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (r : ℝ)
    (i : ℕ) (hi : m < i) :
    (rawD p q r).coeff i=0 ∧ (rawB p q r).coeff i=0 := by
  have hh : (quotient p q r).coeff i=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (quotient_degree hp hq r) hi)
  simp only [rawD, rawB, coeff_sub, coeff_add, coeff_C_mul, hh, hp.2 i hi, hq.2 i hi]
  constructor <;> ring
end PhosphorylationSharpness
