-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sub_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:03.958802+00:00
-- url     : https://prove2.me/submissions/4e080e2c-5cf3-4611-ad75-da7a58b1298d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_subst_sub_dvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lg_sub_X_low

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
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (k : ℕ)
    (hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ k ∣ α b - β b) (a : Fin d) :
    (PowerSeries.X : PowerSeries C) ^ (k + 1) ∣
      (G.lgCurve α a - G.lgCurve β a) - (α a - β a) := by
  have hA : HasSubst α := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => hα b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => hα b)
  have hB : HasSubst β := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => hβ b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => hβ b)
  have e1 : (G.lgCurve α a - G.lgCurve β a) - (α a - β a) =
      subst α (G.lg a - X a) - subst β (G.lg a - X a) := by
    show subst α (G.lg a) - subst β (G.lg a) - (α a - β a) = _
    rw [MvPowerSeries.subst_sub hA, MvPowerSeries.subst_sub hB, MvPowerSeries.subst_X hA,
      MvPowerSeries.subst_X hB]
    ring
  rw [e1]
  exact subst_sub_dvd _ (coeff_lg_sub_X_low G a) α β hα hβ k hk
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
