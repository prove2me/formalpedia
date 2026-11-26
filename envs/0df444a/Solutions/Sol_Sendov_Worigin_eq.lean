-- Prove2me | solution 1 for Sendov.Worigin_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:57:20.506982+00:00
-- url     : https://prove2.me/submissions/c3e22ae1-7b8d-41cf-93a7-4aecb892dd68

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.Fprod_zero
attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution (n : ℕ) (a x y : ℝ) :
    Worigin n a x y = ((a ^ 2 * ((n : ℝ) - 1) + 1 - a * x : ℝ) : ℂ)
      + ((-(a * y) : ℝ) : ℂ) * I := by
  simp only [Worigin]
  push_cast
  ring
end Sendov
