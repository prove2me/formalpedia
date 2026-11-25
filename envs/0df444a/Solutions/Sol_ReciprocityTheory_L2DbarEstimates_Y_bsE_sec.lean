-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsE_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:29.809137+00:00
-- url     : https://prove2.me/submissions/666a0be4-e97d-4164-a2b9-8ab6352e6099

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_ext_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsD_denom
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
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (h : A.Mset w0 s De → ℂ)
    (hh : Holo n (flatStein A hD hF).z h) (m : ℕ) :
    A.IsSecOn (mu0 + m • L) (A.Mset w0 s De) (bsH (A.Mset w0 s De) h σ w0 m) := by
  have hb := bsD_denom A hD hσ m
  have hh' : Holo n (flatStein A hD hF).z (fun y : A.Mset w0 s De => bsExt (A.Mset w0 s De) h y) := by
    have : (fun y : A.Mset w0 s De => bsExt (A.Mset w0 s De) h y) = h :=
      funext fun y => bsE_ext_mem h y.2
    rw [this]; exact hh
  have hd := (holo_flat_iff A hD hF _).mp hh'
  refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
  · have := (hd i).mul (hb.1 i)
    refine this.congr fun v _ => ?_
    simp [bsH]
  · simp only [bsH]
    have := hb.2 i j y hy hi hj
    simp only at this
    rw [this]; ring
end ReciprocityTheory.L2DbarEstimates.Y
