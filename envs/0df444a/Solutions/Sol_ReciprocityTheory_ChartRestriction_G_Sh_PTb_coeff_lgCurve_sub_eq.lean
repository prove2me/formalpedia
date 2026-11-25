-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lgCurve_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:44.704848+00:00
-- url     : https://prove2.me/submissions/97e13e81-bf96-4951-b836-90c3253a51b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sub_dvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_dvd_of_lgCurve_low

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) {α β : Fin d → PowerSeries C}
    (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (N : ℕ)
    (h : ∀ a, ∀ j < N, PowerSeries.coeff j (G.lgCurve α a) = PowerSeries.coeff j (G.lgCurve β a))
    (a : Fin d) :
    PowerSeries.coeff N (G.lgCurve α a - G.lgCurve β a) = PowerSeries.coeff N (α a - β a) := by
  have hN := dvd_of_lgCurve_low G hα hβ N h
  have h1 := lgCurve_sub_dvd G hα hβ N hN a
  have h2 := PowerSeries.X_pow_dvd_iff.mp h1 N (Nat.lt_succ_self N)
  rw [map_sub] at h2
  exact sub_eq_zero.mp h2
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
