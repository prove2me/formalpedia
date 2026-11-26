-- Prove2me | solution 1 for Sendov.norm_multiset_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:53:34.112568+00:00
-- url     : https://prove2.me/submissions/c18e7fbc-47b3-4e0c-977b-597b60069e50

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun w => ‖w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih => simp [ih]
end Sendov
