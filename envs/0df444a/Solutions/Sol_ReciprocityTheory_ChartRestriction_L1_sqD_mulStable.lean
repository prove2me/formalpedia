-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.sqD_mulStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:14.148417+00:00
-- url     : https://prove2.me/submissions/ed240b41-aabd-4387-a259-1272984e4823

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPoly
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HasCMByStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPrin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sqD_eq
import Theorems.Thm_Formalism_L2_Th1_F_hasCMByStable


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
theorem _root_.solution (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (r : ℕ) : MulStable L ((r : ℂ) + redSqD d) := by
  rw [sqD_eq]
  exact (hasCMByStable d L hCM _ _).1
end ReciprocityTheory.ChartRestriction.L1
