-- Prove2me | solution 1 for PhosphorylationSharpness.quotient_scaled_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:37.582389+00:00
-- url     : https://prove2.me/submissions/108f8407-f3fb-41b5-b047-113a9a9d8e30

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_DensePositive_scaled_limit
import Theorems.Thm_PhosphorylationSharpness_quotient_zero
import Theorems.Thm_PhosphorylationSharpness_quotient_succ

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (quotient p q r).coeff i / r^m) atTop
      (𝓝 (p.coeff m*q.coeff i)) := by
  induction i with
  | zero =>
    have h := hp.scaled_limit.mul_const (q.coeff 0)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [quotient_zero p q (ne_of_gt hr)]
    ring
  | succ i ih =>
    have h := (hp.scaled_limit.mul_const (q.coeff (i+1))).add
      ((ih.sub (hq.scaled_limit.mul_const (p.coeff i))).mul tendsto_inv_atTop_zero)
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [quotient_succ p q (ne_of_gt hr)]
    field_simp
end PhosphorylationSharpness
