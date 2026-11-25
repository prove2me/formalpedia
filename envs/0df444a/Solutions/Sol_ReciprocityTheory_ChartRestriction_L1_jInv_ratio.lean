-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.jInv_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:38:03.830184+00:00
-- url     : https://prove2.me/submissions/6e80eaea-25eb-4fb2-8a97-df99e7df4260

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
theorem _root_.solution (L : PeriodPair) (h3 : L.g₃ ≠ 0) :
    27 * jInv L / (jInv L - 1728) = L.g₂ ^ 3 / L.g₃ ^ 2 := by
  have hD := discNeZero L
  rw [jInv_sub_1728_eq_div]
  unfold jInv
  field_simp
end ReciprocityTheory.ChartRestriction.L1
