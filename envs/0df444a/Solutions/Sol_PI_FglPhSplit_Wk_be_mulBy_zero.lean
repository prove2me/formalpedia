-- Prove2me | solution 1 for PI.FglPhSplit.Wk.be_mulBy_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:45:09.269198+00:00
-- url     : https://prove2.me/submissions/112da73d-edce-4da2-9ff0-7f0a39caaa1c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Theorems.Thm_PI_FglPhSplit_Wk_subst_zero_of
import Theorems.Thm_PI_FglPhSplit_Wk_pt_lg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
namespace PI.FglPhSplit.Wk
theorem _root_.solution (g : Dat K) {τ : Type} (hex0 : PowerSeries.constantCoeff g.ex = 0)
    (hph0 : PowerSeries.constantCoeff g.ph = 0) (hl0 : PowerSeries.constantCoeff g.l = 0)
    (hinv : PowerSeries.subst g.l g.ex = PowerSeries.X) (x : MvPowerSeries τ K)
    {y : MvPowerSeries τ K} (hy : MvPowerSeries.constantCoeff y = 0) :
    g.be (g.mulBy 0 x) y = 0 := by
  have hm : g.mulBy 0 x = 0 := by
    simp only [Dat.mulBy, map_zero, zero_mul, Dat.pt]
    exact subst_zero_of g.ex hex0
  have hlg0 : g.lg (0 : MvPowerSeries τ K) = 0 := subst_zero_of g.l hl0
  have hadd : g.add 0 y = y := by
    simp only [Dat.add, hlg0, zero_add]
    exact pt_lg g hl0 hinv hy
  have hph : g.phAt (0 : MvPowerSeries τ K) = 0 := subst_zero_of g.ph hph0
  simp only [Dat.be, hm, hadd, hph, sub_zero, sub_self]
end PI.FglPhSplit.Wk
