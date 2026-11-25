-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.leviAt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:12:35.943458+00:00
-- url     : https://prove2.me/submissions/4acd7775-4841-443d-abd7-10237af090c7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_wdb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_add


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
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (f g : Y → ℝ) (y : Y)
    (hf : ContDiffAt ℝ 2 (f ∘ (A.chart i).symm) (A.chart i y))
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart i).symm) (A.chart i y)) (ξ : Fin n → ℂ) :
    A.leviAt i (fun x => f x + g x) y ξ = A.leviAt i f y ξ + A.leviAt i g y ξ := by

  unfold WeightedAtlas.leviAt
  rw [← Complex.add_re]
  congr 1
  simp only [Complex.ofReal_add]
  have hf1 : ContDiffAt ℝ 2 (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ)) (A.chart i y) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have hg1 : ContDiffAt ℝ 2 (fun v => ((g ((A.chart i).symm v) : ℝ) : ℂ)) (A.chart i y) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  unfold leviV
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : wdb n k (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ) + ((g ((A.chart i).symm v) : ℝ) : ℂ))
      =ᶠ[𝓝 (A.chart i y)] fun v => wdb n k (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ)) v +
        wdb n k (fun v => ((g ((A.chart i).symm v) : ℝ) : ℂ)) v := by
    filter_upwards [hf1.eventually (by simp), hg1.eventually (by simp)] with v a b
    exact wdb_add (a.differentiableAt (by simp)) (b.differentiableAt (by simp))
  rw [wd_congr hw, wd_add (differentiableAt_wdb hf1) (differentiableAt_wdb hg1)]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
