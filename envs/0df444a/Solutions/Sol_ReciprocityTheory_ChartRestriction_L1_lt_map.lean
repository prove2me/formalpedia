-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.lt_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:08.265343+00:00
-- url     : https://prove2.me/submissions/08b8af77-eac3-41d4-9f84-51ef544a6ce0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ltLog_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_map_subst_ps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ltLog_map

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
theorem _root_.solution (l : ℕ) (hl : 2 ≤ l) (ε : K) :
    PowerSeries.map φ ((uSer g2 g3).subst (C ε * ltLog K l))
      = (uSer (φ g2) (φ g3)).subst (C (φ ε) * ltLog L l) := by
  have h0 : constantCoeff (C ε * ltLog K l) = 0 := by
    rw [map_mul, constantCoeff_C, ltLog_const l hl, mul_zero]
  rw [map_subst_ps φ h0, uSer_map, map_mul, map_C, ltLog_map]
end ReciprocityTheory.ChartRestriction.L1
