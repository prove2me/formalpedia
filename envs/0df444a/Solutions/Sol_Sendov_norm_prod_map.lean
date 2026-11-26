-- Prove2me | solution 1 for Sendov.norm_prod_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:54:18.15199+00:00
-- url     : https://prove2.me/submissions/a41c6f11-c978-4441-b256-3c76adb38688

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_norm_multiset_prod

set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun w => ‖f w‖)).prod := by
  rw [norm_multiset_prod, Multiset.map_map]
  rfl
end Sendov
