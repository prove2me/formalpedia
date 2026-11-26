-- Prove2me | solution 1 for Sendov.norm_sum_map_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:56:54.844298+00:00
-- url     : https://prove2.me/submissions/de022a26-ddf9-4550-af51-d7c1dc9dac99

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).sum‖ ≤ (s.map (fun w => ‖f w‖)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    linarith [norm_add_le (f v) ((t.map f).sum), ih]
end Sendov
