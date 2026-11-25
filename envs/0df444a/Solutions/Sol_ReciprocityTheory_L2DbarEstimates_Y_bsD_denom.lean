-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsD_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:03:03.694014+00:00
-- url     : https://prove2.me/submissions/0a8591da-f3c0-4360-9d28-da6c83614fee

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_isSecOn_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_tr_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_tr_pow


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
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (m : ℕ) :
    A.IsSecOn (mu0 + m • L) (A.Mset w0 s De) (fun i y => σ i y * w0 i y ^ m) := by
  have hw := bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ (A.Mset w0 s De))
  refine ⟨fun i => ?_, ?_⟩
  · have h := (hσ.1.1 i).mul ((hw.1 i).pow m)
    refine h.congr fun v _ => ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
  · intro i j y hy hi hj
    have h := bsA_tr_mul A hσ.1.2 (bsA_tr_pow A hw.2 m) i j y hy hi hj
    simpa only using h
end ReciprocityTheory.L2DbarEstimates.Y
