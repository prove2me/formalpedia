-- Prove2me | solution 1 for PhosphorylationSharpness.rawB_scaled_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:30:01.136356+00:00
-- url     : https://prove2.me/submissions/64c8204c-c6b6-42c2-9ae0-d24d0c5a7c45

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_DensePositive_scaled_limit
import Theorems.Thm_PhosphorylationSharpness_rawD_scaled_limit

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (rawB p q r).coeff i/r^(m+1)) atTop
      (𝓝 (4*p.coeff m*(q.coeff i+p.coeff i))) := by
  have h := ((rawD_scaled_limit hp hq i).add
      ((hp.scaled_limit.mul_const (p.coeff i)).const_mul 4)).sub
    (((hq.scaled_limit.mul_const (p.coeff i+q.coeff i)).const_mul 2).mul
      tendsto_inv_atTop_zero)
  have he : 4*p.coeff m*q.coeff i+4*(p.coeff m*p.coeff i)-
      2*(q.coeff m*(p.coeff i+q.coeff i))*0 =
      4*p.coeff m*(q.coeff i+p.coeff i) := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  simp only [rawB, rawD, coeff_add, coeff_sub, coeff_C_mul, pow_succ]
  field_simp
  ring
end PhosphorylationSharpness
