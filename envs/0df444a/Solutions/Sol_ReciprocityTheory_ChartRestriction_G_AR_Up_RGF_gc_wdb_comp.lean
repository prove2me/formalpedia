-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_wdb_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:28.116337+00:00
-- url     : https://prove2.me/submissions/cc7dcedb-031e-486f-9c5d-a0e53987b53a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPfA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_clm_decomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
open Filter Topology Set ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
theorem _root_.solution (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wdb n j (g ∘ F) v = ∑ a, wdb d a g (F v) * (starRingEnd ℂ) (J (bas n j) a) := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wdb, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination ((D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 -
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq
end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
