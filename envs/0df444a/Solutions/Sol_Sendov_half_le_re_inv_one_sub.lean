-- Prove2me | solution 1 for Sendov.half_le_re_inv_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:16.85184+00:00
-- url     : https://prove2.me/submissions/d5e5e7b3-dab6-4a3b-82f8-95e9541cf1f8

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
theorem _root_.solution {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    (1 : ℝ) / 2 ≤ (((1 : ℂ) - z)⁻¹).re := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hd : 0 < Complex.normSq ((1 : ℂ) - z) := Complex.normSq_pos.2 hne
  have hsq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at h
    nlinarith [hz, norm_nonneg z, h]
  rw [Complex.inv_re, le_div_iff₀ hd, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith [hsq]
end Sendov
