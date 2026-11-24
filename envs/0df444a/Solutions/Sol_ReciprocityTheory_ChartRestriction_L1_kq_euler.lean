-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kq_euler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:19.850999+00:00
-- url     : https://prove2.me/submissions/0fc8cb7b-5066-4883-9372-4b48dc4660ec

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
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d : ℕ) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) : (-(d : ZMod l)) ^ (l / 2) = -1 := by
  have hd0 : (-(d : ZMod l)) ≠ 0 := by
    rw [neg_ne_zero]
    intro h0
    apply hld
    exact (CharP.cast_eq_zero_iff (ZMod l) l d).mp h0
  rcases ZMod.pow_div_two_eq_neg_one_or_one l hd0 with h | h
  all_goals first
    | exact h
    | (exfalso
       obtain ⟨a, ha⟩ := (ZMod.euler_criterion l hd0).mpr h
       exact hin ⟨a, by rw [ha, sq]⟩)
end ReciprocityTheory.ChartRestriction.L1
