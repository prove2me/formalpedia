-- Prove2me | solution 1 for Sendov.Fprod_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:56:15.289977+00:00
-- url     : https://prove2.me/submissions/39c3ca28-5d3c-48c9-9f6a-23a47bf7c5f4

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero


attribute [local simp] Sendov.sumEraseProdC_zero

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℝ) (q : Multiset ℂ) : Fprod a q 0 = 1 := by
  simp [Fprod]
end Sendov
