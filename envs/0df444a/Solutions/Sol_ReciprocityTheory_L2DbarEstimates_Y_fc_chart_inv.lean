-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_chart_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:58:41.737143+00:00
-- url     : https://prove2.me/submissions/8552af41-26fd-4d25-9fcb-07b3bdc8b591

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_isOpen_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_jz_det_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_mem_O

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
    (hF : A.Flat w0 s De)
    (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n)) (he : IsChart n (fun y : A.Mset w0 s De => A.zmap w0 s y) e)
    (x : A.Mset w0 s De) (hxe : x ∈ e.source) (i : ι) (hxi : (x : Y) ∈ (A.chart i).source) :
    ∃ G : V n → V n, ContDiffAt ℂ ∞ G (e x) ∧ G (e x) = A.chart i x ∧
      ∀ᶠ w in 𝓝 (e x), ((e.symm w : A.Mset w0 s De) : Y) = (A.chart i).symm (G w) := by
  have hO := fc_isOpen_O A (De := De) hD i
  have hmO := fc_mem_O A x i hxi
  have hcd : ContDiffAt ℂ ∞ (A.zLoc w0 s i) (A.chart i x) :=
    (fc_zLoc_contDiffOn A hD i).contDiffAt (hO.mem_nhds hmO)
  have hdet := fc_jz_det_ne A hD hF x.2 i hxi
  let f' : V n ≃L[ℂ] V n :=
    (fderiv ℂ (A.zLoc w0 s i) (A.chart i x)).toContinuousLinearEquivOfDetNeZero hdet
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := WithTop.coe_ne_zero.mpr (by simp)
  have hf' : HasFDerivAt (A.zLoc w0 s i) (f' : V n →L[ℂ] V n) (A.chart i x) := by
    simp only [f', ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hcd.differentiableAt hn).hasFDerivAt
  have hs : HasStrictFDerivAt (A.zLoc w0 s i) (f' : V n →L[ℂ] V n) (A.chart i x) :=
    hcd.hasStrictFDerivAt' hf' hn
  have hloc := hcd.to_localInverse hf' hn
  have hzx : A.zLoc w0 s i (A.chart i x) = e x := fc_zLoc_chart A hD e he x hxe i hxi
  have hsymmc : ContinuousAt (fun w => ((e.symm w : A.Mset w0 s De) : Y)) (e x) :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm (e.map_source hxe))
  have hGc : Filter.Tendsto (fun w => A.chart i (e.symm w : Y)) (𝓝 (e x)) (𝓝 (A.chart i x)) := by
    have h := ((A.chart i).continuousAt hxi).comp_of_eq hsymmc (by simp [e.left_inv hxe])
    unfold ContinuousAt at h
    simp only [Function.comp_apply, e.left_inv hxe] at h
    exact h
  have hGx : A.chart i (e.symm (e x) : Y) = A.chart i x := by rw [e.left_inv hxe]
  have hev1 : ∀ᶠ w in 𝓝 (e x), e.symm w ∈ e.source ∧ (e.symm w : Y) ∈ (A.chart i).source := by
    have h1 : ∀ᶠ w in 𝓝 (e x), w ∈ e.target := e.open_target.mem_nhds (e.map_source hxe)
    have h2 : ∀ᶠ w in 𝓝 (e x), ((e.symm w : A.Mset w0 s De) : Y) ∈ (A.chart i).source := by
      apply hsymmc.preimage_mem_nhds
      simp only [e.left_inv hxe]
      exact (A.chart i).open_source.mem_nhds hxi
    filter_upwards [h1, h2] with w hw1 hw2
    exact ⟨e.map_target hw1, hw2⟩
  have hright : ∀ᶠ w in 𝓝 (e x), A.zLoc w0 s i (A.chart i (e.symm w : Y)) = w := by
    filter_upwards [hev1, e.open_target.mem_nhds (e.map_source hxe)] with w hw hwt
    rw [fc_zLoc_chart A hD e he (e.symm w) hw.1 i hw.2, e.right_inv hwt]
  have hleft := hGc.eventually hs.eventually_left_inverse
  refine ⟨fun w => A.chart i (e.symm w : Y), ?_, hGx, ?_⟩
  · have heq : (fun w => A.chart i (e.symm w : Y)) =ᶠ[𝓝 (e x)] hcd.localInverse hf' hn := by
      filter_upwards [hleft, hright] with w h1 h2
      rw [h2] at h1
      exact h1.symm
    rw [hzx] at hloc
    exact hloc.congr_of_eventuallyEq heq
  · filter_upwards [hev1] with w hw
    rw [(A.chart i).left_inv hw.2]
end ReciprocityTheory.L2DbarEstimates.Y
