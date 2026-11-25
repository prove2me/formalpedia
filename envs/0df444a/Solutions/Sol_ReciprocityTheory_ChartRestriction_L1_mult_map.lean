-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.mult_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:04.237818+00:00
-- url     : https://prove2.me/submissions/4a10f8e2-1528-4f20-846e-79419fda492f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_constantCoeff_C_mul_weierstrassLog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_map_subst_ps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lgS_map

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
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (b : K) :
    PowerSeries.map φ ((uSer g2 g3).subst (C b * lgS g2 g3))
      = (uSer (φ g2) (φ g3)).subst (C (φ b) * lgS (φ g2) (φ g3)) := by
  rw [map_subst_ps φ (constantCoeff_C_mul_weierstrassLog g2 g3 b), uSer_map, map_mul, map_C, lgS_map]
end ReciprocityTheory.ChartRestriction.L1
