-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_expX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:42.124462+00:00
-- url     : https://prove2.me/submissions/f8f8e2fc-89e8-41f6-a447-bb5d4dd85806

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_coeff_X_pow

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable (A : Type) [CommRing A] [Algebra ℚ A]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    coeff e (PowerSeries.subst (X i : MvPowerSeries (Fin 2) A) (PowerSeries.exp A)) =
      if e = single i (e i) then algebraMap ℚ A (1 / (e i).factorial) else 0 := by
  have ha : PowerSeries.HasSubst (X i : MvPowerSeries (Fin 2) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.coeff_subst ha]
  simp_rw [gt_coeff_X_pow A i, PowerSeries.coeff_exp]
  rw [finsum_eq_single _ (e i)]
  · split_ifs <;> simp
  · intro m hm
    split_ifs with h
    · exact absurd (by rw [h]; simp) hm
    · simp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
