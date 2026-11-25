-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.tangent_eq_lc_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:04.486579+00:00
-- url     : https://prove2.me/submissions/409f147b-104c-40d4-b9e4-24e26c187dc6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lgCurve_low

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
theorem _root_.solution (G : LogFGL v d) (p : ℕ) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : tangent ga = G.lc p ga 0 := by
  funext a
  show PowerSeries.coeff 1 (ga a) = PowerSeries.coeff (p ^ 0) (G.lgCurve ga a)
  rw [pow_zero]
  exact (coeff_lgCurve_low G le_rfl (fun b i hi => by
    rw [Nat.lt_one_iff.mp hi, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0 b]) a
    (by norm_num)).symm
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
