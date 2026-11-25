-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.exp_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:46:32.522708+00:00
-- url     : https://prove2.me/submissions/b8494d5c-9041-4853-87c4-c16d991136f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAdd

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type} (f : MvPowerSeries σ k)
    (hf : constantCoeff f = 0) :
    ∃ Y : MvPowerSeries σ k, PowerSeries.subst f (PowerSeries.exp k) = 1 + f * Y := by
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf

  set E : PowerSeries k := PowerSeries.mk fun n => algebraMap ℚ k (1 / ((n + 1).factorial : ℚ)) with hE
  have hexp : PowerSeries.exp k = 1 + PowerSeries.X * E := by
    ext n
    rcases n with _ | n
    · simp [PowerSeries.coeff_exp]
    · simp [PowerSeries.coeff_exp, hE, PowerSeries.coeff_succ_X_mul]
  refine ⟨PowerSeries.subst f E, ?_⟩
  rw [hexp, ← PowerSeries.coe_substAlgHom ha, map_add, map_one, map_mul,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]
end ReciprocityTheory.ChartRestriction.G.TB.G2
