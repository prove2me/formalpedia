-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.wickExp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:02.986805+00:00
-- url     : https://prove2.me/submissions/e5d6c68e-671f-4008-aad1-c72f80a9d525

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_smul_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_zero_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_sum_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_add_f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_Cmul_f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_sum_f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_iterate_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_half_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_exp_cut

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (hH : HalfSt) : WickExpSt := by
  intro k _ _ d F ι _ u c P q hc hq0 hq1 hq2 t G
  obtain ⟨Y, hY⟩ := exp_cut t q hq0 P.totalDegree
  have hrem : constantCoeff (DpolyOf F u P (G * (q ^ (P.totalDegree + 1) * Y))) = 0 := by
    rw [show G * (q ^ (P.totalDegree + 1) * Y) = (G * Y) * q ^ (P.totalDegree + 1) by ring,
      half_pow hH F u c q hc hq0 hq1 hq2 (P.totalDegree + 1) P (G * Y), iterate_eq_zero,
      dpolyOf_zero_P, map_zero, mul_zero]
  rw [hY, mul_add, dpolyOf_add_f, map_add, hrem, add_zero, Finset.mul_sum, dpolyOf_sum_f, map_sum]
  unfold expSecond
  rw [dpolyOf_sum_P, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_left_comm G, dpolyOf_Cmul_f, map_mul, MvPowerSeries.constantCoeff_C,
    half_pow hH F u c q hc hq0 hq1 hq2 n P G, dpolyOf_smul_P, map_mul, MvPowerSeries.constantCoeff_C]
  ring
end ReciprocityTheory.ChartRestriction.G.TB.GE
