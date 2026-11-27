-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.exp_neg_psD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:40:47.20474+00:00
-- url     : https://prove2.me/submissions/ff772c29-c249-4ebc-86b2-ea015d102d6c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_aap_sqn_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_aap_sqn_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (ps1 : Y → ℝ) (η : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (y : Y) : Real.exp (-A.psD L w s ps1 η δ y) =
      Real.exp (-ps1 y) * A.sqn L w y ^ (-η) * (A.sqn L s y + δ) ^ (-(n : ℝ)) := by
  have h1 := A.aap_sqn_pos hD y
  have h2 : 0 < A.sqn L s y + δ := by have := A.aap_sqn_nonneg L s y; linarith
  rw [Real.rpow_def_of_pos h1, Real.rpow_def_of_pos h2, ← Real.exp_add, ← Real.exp_add]
  congr 1; unfold psD; ring
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
