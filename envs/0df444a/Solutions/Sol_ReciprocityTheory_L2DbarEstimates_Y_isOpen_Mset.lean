-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.isOpen_Mset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:58.834961+00:00
-- url     : https://prove2.me/submissions/f3fe3b65-89b0-4a2c-be29-e915b45150dd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_continuousOn_sec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_mem_Mset_iff

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
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) : IsOpen (A.Mset w0 s De) := by
  rw [isOpen_iff_mem_nhds]
  intro y0 hy0
  have hU : (A.chart (A.pick y0)).source ∈ 𝓝 y0 :=
    (A.chart (A.pick y0)).open_source.mem_nhds (A.mem_pick y0)
  have hw : ContinuousAt (w0 (A.pick y0)) y0 := (continuousOn_sec hD.isSection_denom _).continuousAt hU
  have hs : ∀ k, ContinuousAt (s k (A.pick y0)) y0 := fun k =>
    (continuousOn_sec (hD.sec_s k) _).continuousAt hU
  have hy0' := (mem_Mset_iff De hD (A.mem_pick y0)).1 hy0
  have hq : ContinuousAt (fun y => MvPolynomial.eval
      (fun k => s k (A.pick y0) y / w0 (A.pick y0) y) De) y0 :=
    (MvPolynomial.continuous_eval De).continuousAt.comp
      (continuousAt_pi.2 fun k => (hs k).div hw hy0'.1)
  filter_upwards [hU, hw.eventually_ne hy0'.1, hq.eventually_ne hy0'.2] with y hyU hyw hyq
  exact (mem_Mset_iff De hD hyU).2 ⟨hyw, hyq⟩
end ReciprocityTheory.L2DbarEstimates.Y
