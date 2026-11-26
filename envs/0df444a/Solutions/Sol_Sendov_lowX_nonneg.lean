-- Prove2me | solution 1 for Sendov.lowX_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:57:42.827667+00:00
-- url     : https://prove2.me/submissions/1f310377-b561-40fb-8525-16a25af88b02

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) : 0 ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  simp only [lowX]
  positivity
end Sendov
