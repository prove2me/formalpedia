-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.dvd_of_lgCurve_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:56.339994+00:00
-- url     : https://prove2.me/submissions/95efcb63-0962-4846-8ebd-74e0f0bbb3e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sub_dvd

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
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) :
    ∀ N : ℕ, (∀ a, ∀ j < N, PowerSeries.coeff j (G.lgCurve α a) =
      PowerSeries.coeff j (G.lgCurve β a)) →
      ∀ a, (PowerSeries.X : PowerSeries C) ^ N ∣ α a - β a
  | 0, _, a => by simp
  | N + 1, h, a => by
      have ih := solution G hα hβ N (fun a j hj => h a j (by omega))
      have h1 := PowerSeries.X_pow_dvd_iff.1 (lgCurve_sub_dvd G hα hβ N ih a) N (by omega)
      rw [map_sub, map_sub, h a N (by omega), sub_self, zero_sub, neg_eq_zero] at h1
      rw [PowerSeries.X_pow_dvd_iff]
      intro j hj
      rcases Nat.lt_succ_iff.1 hj |>.lt_or_eq with hj | rfl
      · exact PowerSeries.X_pow_dvd_iff.1 (ih a) j hj
      · rw [map_sub]; exact h1
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
