-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_phaseLaw_map_arg_exp_mul_b05b5462359a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:36.396015+00:00
-- url     : https://prove2.me/submissions/62415a67-1b8a-4c2c-920b-8e9fb8a2af98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSpherePhase

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
open MeasureTheory ProbabilityTheory Real
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {c : ℂ} (hc : c ≠ 0) :
    phaseLaw.map (fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * c)) = phaseLaw := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have hI : Set.Ioc (-π) (-π + 2 * π) = Set.Ioc (-π) π := by ring_nf
  have h1 := AddCircle.measurePreserving_mk (2 * π) (-π)
  rw [hI] at h1
  have h2 := measurePreserving_add_right (volume : Measure (AddCircle (2 * π)))
    ((Complex.arg c : ℝ) : AddCircle (2 * π))
  have h3 := AddCircle.measurePreserving_equivIoc (T := 2 * π) (a := -π)
  have h4 : MeasurePreserving (Subtype.val : Set.Ioc (-π) (-π + 2 * π) → ℝ)
      (Measure.comap Subtype.val volume) (volume.restrict (Set.Ioc (-π) π)) :=
    ⟨measurable_subtype_coe, by rw [map_comap_subtype_coe measurableSet_Ioc, hI]⟩
  have hcomp := h4.comp (h3.comp (h2.comp h1))
  have hfun : (fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * c)) =
      Subtype.val ∘ (AddCircle.equivIoc (2 * π) (-π)) ∘
        (fun x ↦ x + ((Complex.arg c : ℝ) : AddCircle (2 * π))) ∘
        ((↑) : ℝ → AddCircle (2 * π)) := by
    funext θ
    have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have he : Complex.exp (θ * Complex.I) * c =
        (‖c‖ : ℂ) * Complex.exp (((θ + Complex.arg c : ℝ) : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c]
      rw [mul_left_comm, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, he,
      Complex.arg_real_mul _ hc', Complex.arg_exp]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
    rw [← AddCircle.coe_add]
    rfl
  rw [hfun]
  have hmeas : Measurable (Subtype.val ∘ (AddCircle.equivIoc (2 * π) (-π)) ∘
        (fun x ↦ x + ((Complex.arg c : ℝ) : AddCircle (2 * π))) ∘
        ((↑) : ℝ → AddCircle (2 * π))) := hcomp.measurable
  rw [phaseLaw, ProbabilityTheory.cond, Measure.map_smul, hcomp.map_eq]
end GroundTheory.Heights₂.Heights
