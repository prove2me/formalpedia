-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_expC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:54.22785+00:00
-- url     : https://prove2.me/submissions/0a35ba18-3151-4c51-905c-9b4fbf75b032

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_expC_apply

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
theorem _root_.solution (G : LogFGL v d) {q : ℕ} (hq : q ≠ 0) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) (a : Fin d) :
    G.lgCurve (expC q ga) a = PowerSeries.expand q hq (G.lgCurve ga a) := by
  have hga : HasSubst ga := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => h0 b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => h0 b)
  have hX : HasSubst (fun _ : Unit => (PowerSeries.X ^ q : PowerSeries C)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by first | simp [hq, PowerSeries.X] | (simp [hq]; exact PowerSeries.constantCoeff_X))
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun _ => by first | simp [hq, PowerSeries.X] | (simp [hq]; exact PowerSeries.constantCoeff_X))
  have e1 : ∀ g : PowerSeries C,
      PowerSeries.expand q hq g = PowerSeries.subst (PowerSeries.X ^ q : PowerSeries C) g :=
    fun g => (expC_apply hq (fun _ => g) a).symm
  rw [e1]
  first
  | (show MvPowerSeries.subst (expC q ga) (G.lg a) =
        MvPowerSeries.subst (fun _ => (PowerSeries.X ^ q : PowerSeries C))
          (MvPowerSeries.subst ga (G.lg a))
     rw [MvPowerSeries.subst_comp_subst_apply hga hX]
     rfl)
  | (unfold LogFGL.lgCurve PowerSeries.subst
     rw [MvPowerSeries.subst_comp_subst_apply hga hX]
     rfl)
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
