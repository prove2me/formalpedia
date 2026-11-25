-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_sub_1728_eq_one_of_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:02.29953+00:00
-- url     : https://prove2.me/submissions/b0549efb-9ba4-4db4-b86f-bde86b955bc5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKurOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_G2EqZeroOfHasCMByThree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormWeierstrassCoeffSmallJ
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_norm_1728_eq_one_of_five_le__2df1bf27fa32

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (h5 : 5 ≤ l) {J : ℂ_[l]} (hJ : ‖J‖ < 1) : ‖J - 1728‖ = 1 := by
  have h := norm_1728_eq_one_of_five_le' l h5
  have hne : ‖J‖ ≠ ‖-(1728 : ℂ_[l])‖ := by rw [norm_neg, h]; exact hJ.ne
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, h]
  exact max_eq_right hJ.le
end ReciprocityTheory.ChartRestriction.L1
