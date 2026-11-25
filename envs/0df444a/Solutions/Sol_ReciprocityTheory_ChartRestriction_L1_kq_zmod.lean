-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kq_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:21.972317+00:00
-- url     : https://prove2.me/submissions/d770c8bb-3697-462a-aeb6-74cdb40d3077

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_int_dvd

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
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (n : ℤ) (h : (n : ZMod l) = 0) : ‖(n : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := kq_int_dvd l n ((ZMod.intCast_zmod_eq_zero_iff_dvd n l).mp h)
end ReciprocityTheory.ChartRestriction.L1
