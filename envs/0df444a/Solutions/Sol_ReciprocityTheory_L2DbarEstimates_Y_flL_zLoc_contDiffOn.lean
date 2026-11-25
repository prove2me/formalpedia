-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_zLoc_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:49.961029+00:00
-- url     : https://prove2.me/submissions/8a26e82c-7567-440c-b5c7-b426eb46bc13

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_isOpen_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_comp_diff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holo_contDiffOn_complex


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
theorem _root_.solution (hD : A.D0 L w w0 s) (i : ι) :
    ContDiffOn ℂ ∞ (A.zLoc w0 s i) (flO A w0 i) := by

  unfold WeightedAtlas.zLoc
  rw [contDiffOn_piLp]
  intro k
  simp only [WithLp.ofLp_toLp]
  exact ReciprocityTheory.L2DbarEstimates.C.holo_contDiffOn_complex (flL_isOpen_O A hD i) (flL_comp_diff A hD i k)
end ReciprocityTheory.L2DbarEstimates.Y
