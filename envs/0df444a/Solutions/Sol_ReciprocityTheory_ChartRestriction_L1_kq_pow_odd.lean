-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kq_pow_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:14.52439+00:00
-- url     : https://prove2.me/submissions/18cc6684-1628-49a2-9b21-31000d008418

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub

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
variable {l}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (δ c : ℂ_[l]) (hδ : δ ^ 2 = c) (n m : ℕ) (h : n = 2 * m + 1) :
    δ ^ n = δ * c ^ m := by
  rw [h, pow_succ, pow_mul, hδ, mul_comm]
end ReciprocityTheory.ChartRestriction.L1
