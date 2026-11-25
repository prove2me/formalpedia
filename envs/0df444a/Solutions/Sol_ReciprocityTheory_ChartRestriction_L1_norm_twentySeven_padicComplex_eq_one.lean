-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_twentySeven_padicComplex_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:49:14.576399+00:00
-- url     : https://prove2.me/submissions/f107e9ef-65c3-45fe-b7a7-48d50bef3b02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKur
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedModel
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_red_norm_natCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (h5 : 5 ≤ l) : ‖(27 : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  have h : ¬ l ∣ 27 := by
    intro h
    have h3 : l ∣ 3 := hp.dvd_of_dvd_pow (show l ∣ 3 ^ 3 by simpa using h)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  simpa using red_norm_natCast l h
end ReciprocityTheory.ChartRestriction.L1
