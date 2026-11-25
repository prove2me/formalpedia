-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.evalYZero_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:55.073747+00:00
-- url     : https://prove2.me/submissions/ef6e8a93-a66a-4153-8619-e771095599d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB

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
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (F G : MvPowerSeries (Fin 2) R) : ev0 (F * G) = ev0 F * ev0 G := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  unfold ev0
  rw [MvPowerSeries.subst_mul ha]
end ReciprocityTheory.ChartRestriction.L1
