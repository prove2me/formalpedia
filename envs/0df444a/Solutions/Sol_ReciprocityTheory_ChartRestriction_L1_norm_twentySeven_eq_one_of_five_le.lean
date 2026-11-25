-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_twentySeven_eq_one_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:59.64135+00:00
-- url     : https://prove2.me/submissions/9040769c-f5df-4772-8f3a-bd91c417fe66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKurOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_G2EqZeroOfHasCMByThree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormWeierstrassCoeffSmallJ
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_red_norm_natCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (h5 : 5 ≤ l) : ‖(27 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 27 := by
    intro h
    have h3 : l ∣ 3 := (Fact.out : l.Prime).dvd_of_dvd_pow (show l ∣ 3 ^ 3 by simpa using h)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  simpa using red_norm_natCast l h
end ReciprocityTheory.ChartRestriction.L1
