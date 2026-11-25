-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B2x8__x_map_inv_5a29fa767cc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:13.763803+00:00
-- url     : https://prove2.me/submissions/d5fd99d5-6bc9-49f5-9025-301ebe38806a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_conj_inverse_map_has_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_conj_inverse_map_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_conj_inverse_map_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_conj_inverse_map_image
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_conj_inverse_map_inj_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_restrict_compl_zero_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (l : ℂ) (hl : l ≠ 0) : μx.map (fun c => l / conj c) = μx := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hw : Measurable fun c : ℂ => ENNReal.ofReal ((‖c‖ ^ 2)⁻¹) := by fun_prop
  rw [lintegral_map hg (conj_inverse_map_measurable l)]
  unfold μx
  have hgl : Measurable fun a : ℂ => g (l / conj a) := hg.comp (conj_inverse_map_measurable l)
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hg, lintegral_withDensity_eq_lintegral_mul _ hw hgl]
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure ℂ)
    (s := {(0 : ℂ)}ᶜ) (f := fun c : ℂ => l / conj c) (f' := mi2D l) (MeasurableSet.singleton _).compl
    (fun x hx => (conj_inverse_map_has_fderiv l x hx).hasFDerivWithinAt) (conj_inverse_map_inj_on l hl)
    ((fun c : ℂ => ENNReal.ofReal ((‖c‖ ^ 2)⁻¹)) * g)
  rw [conj_inverse_map_image l hl, restrict_compl_zero_eq] at key
  rw [key]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ c : ℂ, c ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hae] with c hc
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), conj_inverse_map_det, abs_neg]
  congr 2
  have h1 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have h2 : 0 < ‖l‖ := norm_pos_iff.2 hl
  rw [abs_of_nonneg (by positivity), norm_div, RCLike.norm_conj]
  field_simp
end Formalism.FourierDecayAlt.P.B2x8
