-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_holo_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:25.351814+00:00
-- url     : https://prove2.me/submissions/bd5e05c7-75fe-4b6c-ae8e-3e17fc3466a6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ne_of_tr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_tr_ratio
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_holo_flat_iff


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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {la : La} {a b : ι → Y → ℂ}
    (ha : A.IsSecOn la (A.Mset w0 s De) a) (hb : A.IsSecOn la (A.Mset w0 s De) b)
    (hb0 : ∀ y ∈ A.Mset w0 s De, b (A.pick y) y ≠ 0) :
    Holo n (flatStein A hD hF).z
      (fun y : A.Mset w0 s De => a (A.pick (y : Y)) y / b (A.pick (y : Y)) y) := by
  rw [holo_flat_iff A hD hF (fun y => a (A.pick y) y / b (A.pick y) y)]
  intro i
  have hne : ∀ v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De,
      (b i ∘ (A.chart i).symm) v ≠ 0 := fun v hv =>
    bsA_ne_of_tr A hb.2 hv.2 ((A.chart i).map_target hv.1) (A.mem_pick _) (hb0 _ hv.2)
  have h3 := (ha.1 i).mul ((hb.1 i).inv hne)
  refine h3.congr fun v hv => ?_
  simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply]
  rw [← div_eq_mul_inv]
  exact bsA_tr_ratio A ha.2 hb.2 hv.2 (A.mem_pick _) ((A.chart i).map_target hv.1)
end ReciprocityTheory.L2DbarEstimates.Y
