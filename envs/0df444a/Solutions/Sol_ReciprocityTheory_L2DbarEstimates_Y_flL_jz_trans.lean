-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_jz_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:54:02.656479+00:00
-- url     : https://prove2.me/submissions/dbcf458f-dd6d-4945-b8d5-64482243e48b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_zLoc_contDiffAt
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
    jz A w0 s j y = (jz A w0 s i y).comp
      (fderiv ℂ (A.chart i ∘ (A.chart j).symm) (A.chart j y)) := by

  unfold jz
  have hp : A.chart i ((A.chart j).symm (A.chart j y)) = A.chart i y := by
    rw [(A.chart j).left_inv hj]
  have hO : IsOpen (ovl A.chart j i) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (A.chart i).open_source
  have hm : A.chart j y ∈ ovl A.chart j i := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j y) ∈ (A.chart i).source
    rw [(A.chart j).left_inv hj]
    exact hi
  have hT : DifferentiableAt ℂ (A.chart i ∘ (A.chart j).symm) (A.chart j y) :=
    (A.holo_trans j i).differentiableAt (hO.mem_nhds hm)
  have hZ : DifferentiableAt ℂ (A.zLoc w0 s i) ((A.chart i ∘ (A.chart j).symm) (A.chart j y)) := by
    rw [Function.comp_apply, hp]
    exact (flL_zLoc_contDiffAt A hD hy hi).differentiableAt (by simp)
  have hE : A.zLoc w0 s j =ᶠ[𝓝 (A.chart j y)] A.zLoc w0 s i ∘ (A.chart i ∘ (A.chart j).symm) := by
    filter_upwards [hO.mem_nhds hm] with v hv
    have hpj : (A.chart j).symm v ∈ (A.chart j).source := (A.chart j).map_target hv.1
    have hpi : (A.chart j).symm v ∈ (A.chart i).source := hv.2
    simp only [WeightedAtlas.zLoc, Function.comp_apply, (A.chart i).left_inv hpi]
    congr 1
    funext k
    have hw := hD.isSection_denom
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw hs
    rw [hw.2 j i _ trivial hpj hpi, hs.2 j i _ trivial hpj hpi]
    exact mul_div_mul_left _ _ (A.g_ne L j i _ hpj hpi)
  rw [hE.fderiv_eq, fderiv_comp _ hZ hT, Function.comp_apply, hp]
end ReciprocityTheory.L2DbarEstimates.Y
