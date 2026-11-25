-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_lambda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:42.019709+00:00
-- url     : https://prove2.me/submissions/38a426ef-4d91-474b-be5e-5f6be70463b1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_holo_ratio
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_isSecOn_mono


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
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hLSE : LSEAll.{u} n) :
    SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      Real.log (∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2)) ∧
    LeviNonneg n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      Real.log (∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2)) := by
  have hg : ∀ k, Holo n (flatStein A hD hF).z
      (fun y : A.Mset w0 s De => w k (A.pick (y : Y)) y / w0 (A.pick (y : Y)) y) := fun k =>
    bsB_holo_ratio A hD hF (bsA_isSecOn_mono A (hD.sec_w k) (Set.subset_univ _))
      (bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ _)) fun y hy => hy.1
  have hpos : ∀ x : A.Mset w0 s De, 0 < ∑ i : Fin 0, Real.exp ((Fin.elim0 i : A.Mset w0 s De → ℝ) x) +
      ∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2 := by
    intro x
    obtain ⟨k, hk⟩ := hD.no_common_zero x
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ k))
    have : w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x ≠ 0 := div_ne_zero hk x.2.1
    positivity
  have h := hLSE (A.Mset w0 s De) (flatStein A hD hF).z (flatStein A hD hF).isLocalHomeomorph 0 N
    (fun i => Fin.elim0 i) (fun k y => w k (A.pick (y : Y)) y / w0 (A.pick (y : Y)) y)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hg hpos
  simpa using h
end ReciprocityTheory.L2DbarEstimates.Y
