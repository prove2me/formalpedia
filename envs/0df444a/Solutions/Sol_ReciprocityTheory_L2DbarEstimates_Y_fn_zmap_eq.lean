-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_zmap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:55:02.132802+00:00
-- url     : https://prove2.me/submissions/29dac24c-03a1-4787-8f3f-3c93dd704838

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
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
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.zmap w0 s y = WithLp.toLp 2 (fun k => s k i y / w0 i y) := by
  obtain ⟨-, htr0⟩ : A.IsSecOn L Set.univ w0 := hD.isSection_denom
  have hg := A.g_ne L (A.pick y) i y (A.mem_pick y) hy
  unfold zmap
  congr 1
  funext k
  obtain ⟨-, htrk⟩ : A.IsSecOn L Set.univ (s k) := hD.sec_s k
  rw [htrk (A.pick y) i y trivial (A.mem_pick y) hy, htr0 (A.pick y) i y trivial (A.mem_pick y) hy,
    mul_div_mul_left _ _ hg]
end ReciprocityTheory.L2DbarEstimates.Y
