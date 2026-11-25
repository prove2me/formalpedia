-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_det_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:07:05.927269+00:00
-- url     : https://prove2.me/submissions/ab161943-d83f-473f-bd7a-06827efd8f89

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_jz_trans

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
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) {y : Y} (hy : y ∈ A.Mset w0 s De) {i j : ι}
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    (jz A w0 s i y).det = (jz A w0 s j y).det * A.g A.kap i j y := by

  rw [flL_jz_trans A hD hy hj hi, A.g_kap i j y hi hj]
  simp only [ContinuousLinearMap.det]
  exact LinearMap.det_comp _ _
end ReciprocityTheory.L2DbarEstimates.Y
