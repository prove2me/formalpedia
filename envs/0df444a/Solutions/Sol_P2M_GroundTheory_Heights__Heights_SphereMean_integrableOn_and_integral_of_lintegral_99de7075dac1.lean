-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integrableOn_and_integral_of_lintegral_99de7075dac1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:52.370326+00:00
-- url     : https://prove2.me/submissions/5f4a7024-c953-49a7-9a65-fdddaea91bd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution {n : ℕ} {B : Set (Fin n → ℂ)}
    (hB : MeasurableSet B) (hBt : volume B ≠ ⊤) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (hnn : ∀ x ∈ B, 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ x in B, ENNReal.ofReal (f x) = ENNReal.ofReal c * volume B) :
    IntegrableOn f B ∧ ∫ x in B, f x = c * volume.real B := by
  have hnn' : 0 ≤ᵐ[volume.restrict B] f :=
    (ae_restrict_iff' hB).mpr (Filter.Eventually.of_forall hnn)
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn').mpr ?_⟩, ?_⟩
  · rw [h]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBt.lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn' hf.aestronglyMeasurable, h, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc, measureReal_def]
end GroundTheory.Heights₂.Heights.SphereMean
