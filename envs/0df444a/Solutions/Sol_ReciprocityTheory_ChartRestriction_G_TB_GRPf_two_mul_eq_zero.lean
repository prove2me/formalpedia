-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.two_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:31.972141+00:00
-- url     : https://prove2.me/submissions/a7100d20-99ed-4276-a9aa-082808421afb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution {x : k} (h : 2 * x = 0) : x = 0 := by
  have h2 : algebraMap ℚ k (1 / 2) * 2 = 1 := by
    rw [show (2 : k) = algebraMap ℚ k 2 from (map_ofNat (algebraMap ℚ k) 2).symm, ← map_mul]
    norm_num
  calc x = (algebraMap ℚ k (1 / 2) * 2) * x := by rw [h2, one_mul]
    _ = algebraMap ℚ k (1 / 2) * (2 * x) := by ring
    _ = 0 := by rw [h, mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
