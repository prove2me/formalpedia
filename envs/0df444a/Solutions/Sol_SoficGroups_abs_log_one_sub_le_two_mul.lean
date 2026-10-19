-- Prove2me | solution 1 for SoficGroups.abs_log_one_sub_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/edba1ba0-14cf-4156-8c0c-24cedefc8ad8

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
    (eta : ℝ) (heta0 : 0 ≤ eta) (hetaHalf : eta ≤ (1 : ℝ) / 2) :
    |Real.log (1 - eta)| ≤ 2 * eta := by
  have hfactor : 0 < 1 - eta := by linarith
  have hlog : Real.log (1 - eta) ≤ 0 :=
    Real.log_nonpos hfactor.le (by linarith)
  rw [abs_of_nonpos hlog]
  have hlower := Real.one_sub_inv_le_log_of_pos hfactor
  have hratio : eta / (1 - eta) ≤ 2 * eta := by
    apply (div_le_iff₀ hfactor).2
    nlinarith [mul_nonneg heta0 (by linarith : 0 ≤ 1 - 2 * eta)]
  have hidentity : (1 - eta)⁻¹ - 1 = eta / (1 - eta) := by
    field_simp
    ring
  linarith
end SoficGroups
