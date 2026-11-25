-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.sum_four_indices_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:34.764482+00:00
-- url     : https://prove2.me/submissions/7685e18d-98a5-4bdc-8a65-6501db986152

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPfA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


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
theorem _root_.solution (n d : ℕ) (f : Fin n → Fin n → Fin d → Fin d → ℂ) :
    ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := by
  calc ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ j, ∑ k, ∑ b, ∑ a, f j k a b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ k, ∑ a, f j k a b := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ a, f j k a b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ a, ∑ k, f j k a b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := Finset.sum_congr rfl fun b _ => Finset.sum_comm
end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
