-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.evalYZero_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:58.841002+00:00
-- url     : https://prove2.me/submissions/b6ebe7c3-fd81-4d1d-af73-3f80affcb676

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
theorem _root_.solution (φ : PowerSeries R) {P : MvPowerSeries (Fin 2) R}
    (hP : MvPowerSeries.constantCoeff P = 0) : ev0 (φ.subst P) = φ.subst (ev0 P) := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  have hP' : MvPowerSeries.HasSubst (fun _ : Unit => P) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hP)
  unfold ev0
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply hP' ha φ
end ReciprocityTheory.ChartRestriction.L1
