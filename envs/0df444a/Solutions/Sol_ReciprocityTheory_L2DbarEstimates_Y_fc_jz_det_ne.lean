-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_jz_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:45:11.37356+00:00
-- url     : https://prove2.me/submissions/3dad74aa-868b-4bb6-9d95-31b58a2b2f4e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_det_jz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) {y : Y} (hy : y ∈ A.Mset w0 s De) (i : ι)
    (hi : y ∈ (A.chart i).source) : (fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det ≠ 0 := by
  rw [fc_det_jz A hD hy i (A.pick y) hi (A.mem_pick y)]
  exact mul_ne_zero (hF.deriv_ne y hy) (A.g_ne A.kap i (A.pick y) y hi (A.mem_pick y))
end ReciprocityTheory.L2DbarEstimates.Y
