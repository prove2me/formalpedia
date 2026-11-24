-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_sub_le_max_Cl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:02:59.818427+00:00
-- url     : https://prove2.me/submissions/eb437398-65b8-4915-9bbf-7c7ff7a81506

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (a b : ℂ_[l]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ :=
  by simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)
end ReciprocityTheory.ChartRestriction.L1
