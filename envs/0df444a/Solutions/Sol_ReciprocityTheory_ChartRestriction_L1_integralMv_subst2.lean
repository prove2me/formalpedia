-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralMv_subst2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:43.490042+00:00
-- url     : https://prove2.me/submissions/315fbb80-6e86-435a-a5ce-dfc2b9fa91db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_subst2

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : IntegralMv F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : IntegralMv (F.subst P) := by
  rw [integralMv_iff_divBy_one] at hF ⊢
  exact divByMv_subst2 hF hP0 hP
end ReciprocityTheory.ChartRestriction.L1
