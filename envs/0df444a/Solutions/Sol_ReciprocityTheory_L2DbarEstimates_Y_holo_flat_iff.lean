-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.holo_flat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:38.499489+00:00
-- url     : https://prove2.me/submissions/b602d899-dec7-4410-9172-6ff7c7896a15

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_chart_fwd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_chart_inv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_isOpen_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_mem_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart


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
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (u : Y → ℂ) :
    Holo n (flatStein A hD hF).z (fun y : A.Mset w0 s De => u y) ↔
      ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  constructor
  · intro hH i v hv
    set m : A.Mset w0 s De := ⟨(A.chart i).symm v, hv.2⟩
    have hmi : (m : Y) ∈ (A.chart i).source := (A.chart i).map_target hv.1
    have hcm : A.chart i m = v := (A.chart i).right_inv hv.1
    obtain ⟨e, he, hme⟩ := exists_chart n (flatStein A hD hF).z
      (flatStein A hD hF).isLocalHomeomorph m
    have hfw := fc_chart_fwd A hD e he m hme i hmi
    rw [hcm] at hfw
    have hZ := fc_zLoc_chart A hD e he m hme i hmi
    rw [hcm] at hZ
    have hd1 : DifferentiableAt ℂ ((fun y : A.Mset w0 s De => u y) ∘ e.symm)
        (A.zLoc w0 s i v) := by
      rw [hZ]
      exact (hH e he).differentiableAt (e.open_target.mem_nhds (e.map_source hme))
    have hd2 : DifferentiableAt ℂ (A.zLoc w0 s i) v :=
      ((fc_zLoc_contDiffOn A hD i).differentiableOn (by simp)).differentiableAt
        ((fc_isOpen_O A hD i).mem_nhds hv)
    refine ((hd1.comp v hd2).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hfw] with v' hv'
    simp only [Function.comp_apply]
    rw [hv']
  · intro hd e he w hw
    have hme : e.symm w ∈ e.source := e.map_target hw
    have hem : e (e.symm w) = w := e.right_inv hw
    have hmi : ((e.symm w : A.Mset w0 s De) : Y) ∈ (A.chart (A.pick (e.symm w : Y))).source :=
      A.mem_pick _
    obtain ⟨G, hG, hGx, hGe⟩ := fc_chart_inv A hD hF e he _ hme _ hmi
    rw [hem] at hG hGx hGe
    have hd1 : DifferentiableAt ℂ (u ∘ (A.chart (A.pick (e.symm w : Y))).symm) (G w) := by
      rw [hGx]
      exact (hd _).differentiableAt ((fc_isOpen_O A hD _).mem_nhds (fc_mem_O A _ _ hmi))
    refine ((hd1.comp w (hG.differentiableAt (by simp))).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hGe] with w' hw'
    simp only [Function.comp_apply]
    rw [hw']
end ReciprocityTheory.L2DbarEstimates.Y
