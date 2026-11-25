-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsE_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:48:05.942564+00:00
-- url     : https://prove2.me/submissions/61f86e35-957a-4ac8-92e7-058c5921f1ff

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_sec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_sqn_s_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_sqn_cont
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_sqn_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsC_nsq_contOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_Mset


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
open Classical
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (h : A.Mset w0 s De → ℂ) (hh : Holo n (flatStein A hD hF).z h) :
    Measurable ((A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y * bsW A L w s T' y))
      (fun _ => 0)) := by
  have hMo := isOpen_Mset A (De := De) hD
  have h1 := bsC_nsq_contOn A (bsE_sec A hD hF hσ h hh (T' - 1)) hMo
  have h2 : ContinuousOn (bsW A L w s T') (A.Mset w0 s De) := by
    unfold bsW
    refine ContinuousOn.mul ?_ ?_
    · exact (bsA_sqn_cont A hD.sec_s).continuousOn.rpow_const fun x hx =>
        Or.inl (bsE_sqn_s_pos A hD hF hσ hX hx).ne'
    · exact (bsA_sqn_cont A hD.sec_w).continuousOn.rpow_const fun x _ =>
        Or.inl (bsA_sqn_pos A (hD.no_common_zero x)).ne'
  exact ContinuousOn.measurable_piecewise
    (ENNReal.continuous_ofReal.comp_continuousOn (h1.mul h2)) continuousOn_const hMo.measurableSet
end ReciprocityTheory.L2DbarEstimates.Y
