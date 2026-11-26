-- Prove2me | solution 1 for Sendov.eq_one_of_re_eq_one_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:21.278814+00:00
-- url     : https://prove2.me/submissions/2b592fdf-9151-4d35-9801-8decb0d9753f

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {v : ℂ} (hre : v.re = 1) (hv : ‖v‖ ≤ 1) : v = 1 := by
  have hsq : v.re ^ 2 + v.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq v
    rw [Complex.normSq_apply] at h
    nlinarith [hv, norm_nonneg v, h]
  have him : v.im = 0 := by nlinarith [hsq, hre, sq_nonneg v.im]
  apply Complex.ext <;> simp [hre, him]
end Sendov
