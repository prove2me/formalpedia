-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lgCurve_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:31.526793+00:00
-- url     : https://prove2.me/submissions/c3b81957-8a20-44fe-b5ac-0aeef2751d31

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_unit_finsupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_order_lg_sub_X

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
theorem _root_.solution (G : LogFGL v d) {ga : Fin d → PowerSeries C} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ b, ∀ i < k, PowerSeries.coeff i (ga b) = 0) (a : Fin d) {j : ℕ} (hj : j < 2 * k) :
    PowerSeries.coeff j (G.lgCurve ga a) = PowerSeries.coeff j (ga a) := by
  have h0 : ∀ b, constantCoeff (ga b) = 0 := fun b => by
    have := hk b 0 hk1
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  have hs : HasSubst ga := hasSubst_of_constantCoeff_zero h0
  have hsplit : G.lgCurve ga a = ga a + subst ga (G.lg a - X a) := by
    rw [LogFGL.lgCurve, subst_sub hs, subst_X hs]; ring
  have hord : ((k : ℕ∞)) ≤ ⨅ b, MvPowerSeries.order (ga b) := le_iInf fun b => nat_le_order fun e he => by
    rw [unit_finsupp e] at he ⊢
    rw [Finsupp.degree_single] at he
    exact hk b _ he
  have hR := le_order_subst hs (G.lg a - X a)
  have hlt : ((Finsupp.single () j).degree : ℕ∞) < (subst ga (G.lg a - X a)).order := by
    rw [Finsupp.degree_single]
    refine lt_of_lt_of_le ?_ (le_trans (mul_le_mul' hord (order_lg_sub_X G a)) hR)
    exact_mod_cast (show j < k * 2 by omega)
  rw [hsplit, map_add]
  have := coeff_of_lt_order hlt
  change _ + coeff (Finsupp.single () j) _ = _
  rw [this, add_zero]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
