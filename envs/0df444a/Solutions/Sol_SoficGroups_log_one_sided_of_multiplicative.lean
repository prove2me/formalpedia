-- Prove2me | solution 1 for SoficGroups.log_one_sided_of_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/a3466de4-bf0a-4a7c-bbdc-fc9faa13cd94

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (x y eta : ℝ) (hx : 0 < x)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hcomparison : (1 - eta) * x ≤ y) :
    Real.log x - |Real.log (1 - eta)| ≤ Real.log y := by
  have hfactor : 0 < 1 - eta := by linarith
  have hy : 0 < y :=
    lt_of_lt_of_le (mul_pos hfactor hx) hcomparison
  have hlog : Real.log ((1 - eta) * x) ≤ Real.log y :=
    (Real.log_le_log_iff (mul_pos hfactor hx) hy).2 hcomparison
  rw [Real.log_mul hfactor.ne' hx.ne'] at hlog
  have hnonpos : Real.log (1 - eta) ≤ 0 :=
    Real.log_nonpos hfactor.le (by linarith)
  rw [abs_of_nonpos hnonpos]
  linarith
end SoficGroups
