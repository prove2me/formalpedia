-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_contOn_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:50.774362+00:00
-- url     : https://prove2.me/submissions/ddd98950-5a03-409a-b6f6-5737af220961

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero



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
theorem _root_.solution {la : La} {U : Set Y} {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) (i : ι) :
    ContinuousOn (F i) ((A.chart i).source ∩ U) := by
  have h := (hFs.1 i).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left)
    (fun x hx => ⟨(A.chart i).map_source hx.1, by
      show (A.chart i).symm ((A.chart i) x) ∈ U
      rw [(A.chart i).left_inv hx.1]
      exact hx.2⟩)
  refine h.congr fun x hx => ?_
  simp [Function.comp, (A.chart i).left_inv hx.1]
end ReciprocityTheory.L2DbarEstimates.Y
