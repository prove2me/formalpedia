-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_zLoc_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:39:19.075906+00:00
-- url     : https://prove2.me/submissions/9eb36a7b-0226-4920-9694-b7c1972b97aa

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_isOpen_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_zLoc_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_mem_O

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
theorem _root_.solution (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) : ContDiffAt ℂ ∞ (A.zLoc w0 s i) (A.chart i x) := (flL_zLoc_contDiffOn A hD i).contDiffAt ((flL_isOpen_O A hD i).mem_nhds (flL_mem_O A hD hx hi))
end ReciprocityTheory.L2DbarEstimates.Y
