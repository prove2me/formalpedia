-- Prove2me | solution 1 for PhosphorylationSharpness.quotient_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:45.734988+00:00
-- url     : https://prove2.me/submissions/f468ae66-23e4-452d-9ef2-99713b6a3119

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (r : ℝ) :
    (quotient p q r).natDegree ≤ m := by
  have hd : (conversionNumerator p q r).natDegree ≤ m+1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    cases i with
    | zero => omega
    | succ i =>
      simp only [conversionNumerator, coeff_sub, coeff_C_mul, coeff_X_mul]
      rw [hp.2 i (by omega), hq.2 (i+1) (by omega)]
      ring
  rw [quotient, natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
  omega
end PhosphorylationSharpness
