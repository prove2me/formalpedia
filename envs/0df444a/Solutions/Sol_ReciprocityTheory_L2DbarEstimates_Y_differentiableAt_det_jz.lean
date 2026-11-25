-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.differentiableAt_det_jz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:51.829658+00:00
-- url     : https://prove2.me/submissions/c054db01-cee9-4cf7-bc8b-cdfeab930572

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_isOpen_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_zLoc_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_mem_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_det_contDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
section Helpers
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
end Helpers
section Det
variable {n : ℕ}
end Det
private theorem contDiffAt_det_fderiv_zLoc_of_mem_flO {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (i : ι) {v : V n} (hv : v ∈ flO A w0 i) :
    ContDiffAt ℂ ∞ (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det) v := by
  have h := (flL_zLoc_contDiffOn A hD i).contDiffAt ((flL_isOpen_O A hD i).mem_nhds hv)
  exact flL_det_contDiffAt (h.fderiv_right (by simp))
end
end ReciprocityTheory.L2DbarEstimates.Y
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (y : Y) (hy : y ∈ A.Mset w0 s De) (i : ι)
    (hi : y ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i y), DifferentiableAt ℂ (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det) v := by

  filter_upwards [(flL_isOpen_O A hD i).mem_nhds (flL_mem_O A hD hy hi)] with v hv
  exact (contDiffAt_det_fderiv_zLoc_of_mem_flO A hD i hv).differentiableAt (by simp)
end ReciprocityTheory.L2DbarEstimates.Y
