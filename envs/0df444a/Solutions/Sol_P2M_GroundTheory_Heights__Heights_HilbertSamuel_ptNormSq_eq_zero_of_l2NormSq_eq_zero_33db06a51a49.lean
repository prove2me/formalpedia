-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_zero_of_l2NormSq_eq_zero_33db06a51a49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:47.124298+00:00
-- url     : https://prove2.me/submissions/68fe97f6-5d0c-4549-903f-173539dc7a82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_nonneg_d0797495dc03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuous_ptNormSq_cb0742b2cef1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SmoothVolume_isOpenPosMeasure_239f6b264a4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_integrable_ptNormSq_c8a0c94a85ca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
variable [MeasurableSpace X] [BorelSpace X]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (W : Weight L) (dV : SmoothVolume A) [CompactSpace X]
    {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (h0 : sectionL2NormSq W dV n s = 0) (x : X) :
    ptNormSq W n s x = 0 := by
  have := dV.isOpenPosMeasure
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => ptNormSq_nonneg W n s y)
    (integrable_ptNormSq W dV hs)).1 h0
  have := (Continuous.ae_eq_iff_eq (μ := dV.μ) (continuous_ptNormSq W hs) continuous_const).1 hae
  exact congrFun this x
end GroundTheory.Heights₂.Heights.HilbertSamuel
