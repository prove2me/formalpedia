-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.valDiv2_norm_27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:39.101331+00:00
-- url     : https://prove2.me/submissions/56dff243-c837-48ce-b4cc-73e3f24892ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKurOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Norm1728EqOneOfFiveLe
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
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) : ‖(27 : ℂ_[l])‖ = 1 := by
  have hl : l.Prime := Fact.out
  have h : ¬ l ∣ 27 := by
    intro h
    have h12 : l ∣ 3 := hl.dvd_of_dvd_pow (show l ∣ 3 ^ 3 by norm_num; exact h)
    have := Nat.le_of_dvd (by norm_num) h12
    omega
  simpa using red_norm_natCast l h
end ReciprocityTheory.ChartRestriction.L1
