-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:31.598605+00:00
-- url     : https://prove2.me/submissions/913a9970-f631-4069-9ee4-2f9b3fd6082b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_mem_intRing

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
theorem _root_.solution {x : C} (hx : IsIntV v x) {ga : Fin d → PowerSeries C}
    (h : IsCurve v ga) : IsCurve v (rescaleCurve x ga) := by
  intro a
  refine ⟨?_, fun n => ?_⟩
  · show PowerSeries.constantCoeff (PowerSeries.rescale x (ga a)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (h a).1]
  · show IsIntV v (PowerSeries.coeff n (PowerSeries.rescale x (ga a)))
    rw [PowerSeries.coeff_rescale]
    exact mem_intRing.mp (Subring.mul_mem _ (Subring.pow_mem _ (mem_intRing.mpr hx) n)
      (mem_intRing.mpr ((h a).2 n)))
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
