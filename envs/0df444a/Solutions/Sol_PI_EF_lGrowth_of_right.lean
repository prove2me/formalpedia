-- Prove2me | solution 1 for PI.EF.lGrowth_of_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:26.674078+00:00
-- url     : https://prove2.me/submissions/b97d5f37-1c3a-4f7b-a82b-3350654a6107

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthZeta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFinal
import Theorems.Thm_PI_EF_lGrowth_of
import Theorems.Thm_PI_EF_zetaGrowth_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF
namespace PI.EF
theorem _root_.solution (hB : PI.LBoundRight) (hZ : PI.ZetaBoundRight) : LGrowth 7 300000 := by
  have h := lGrowth_of hB (zetaGrowth_of hZ)
  have hm : max (300000 : ℝ) 53946 = 300000 := by norm_num
  rwa [hm] at h
end PI.EF
