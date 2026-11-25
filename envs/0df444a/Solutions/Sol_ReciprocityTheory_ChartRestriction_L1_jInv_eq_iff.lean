-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.jInv_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:08:58.504397+00:00
-- url     : https://prove2.me/submissions/8d79f443-41f4-40d9-a8e6-81fe95078d26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HasCMByStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_jInv_sub_1728_eq_div
import Theorems.Thm_Formalism_L2_Th1_F_discNeZero


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
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) : jInv L = 1728 ↔ L.g₃ = 0 := by
  have hD := discNeZero L
  rw [← sub_eq_zero, jInv_sub_1728_eq_div, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · exact absurd h hD
  · intro h
    left
    rw [h]
    norm_num
end ReciprocityTheory.ChartRestriction.L1
