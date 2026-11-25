-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_integral_complex_norm_pow_div_c13acad093c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:45:37.698081+00:00
-- url     : https://prove2.me/submissions/b513962f-b6b8-44da-b156-512447e20225

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FubiniStudyIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_Ioi_pow_div_add_pow_16caf08408db

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
open MeasureTheory Set Filter Topology Real
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : ℝ) (hc : 0 < c) (k b : ℕ) :
    Integrable (fun w : ℂ => ‖w‖ ^ (2 * b) / (c + ‖w‖ ^ 2) ^ (b + 2 + k)) ∧
    ∫ w : ℂ, ‖w‖ ^ (2 * b) / (c + ‖w‖ ^ 2) ^ (b + 2 + k) =
      π * (((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1)) := by
  obtain ⟨hI, hV⟩ := integral_Ioi_pow_div_add_pow c hc k b
  set f : ℝ → ℝ := fun r => r ^ (2 * b) / (c + r ^ 2) ^ (b + 2 + k) with hf
  set g : ℝ → ℝ := fun t => t ^ b / (c + t) ^ (b + 2 + k) with hg
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hcongr : EqOn (fun x : ℝ => (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ)))
      (fun y : ℝ => (2:ℝ) * (y ^ (Module.finrank ℝ ℂ - 1) • f y)) (Ioi 0) := by
    intro x _
    simp only [hf, hg, hdim, smul_eq_mul]
    rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two, pow_mul]
    norm_num
    ring
  have h2 : IntegrableOn (fun x : ℝ => (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ))) (Ioi 0) :=
    (integrableOn_Ioi_comp_rpow_iff g two_ne_zero).mpr hI
  have h3 := (integrableOn_congr_fun hcongr measurableSet_Ioi).mp h2
  have h4 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • f y) (Ioi 0) := by
    have h5 : IntegrableOn (fun y : ℝ => (1/2 : ℝ) * (2 * (y ^ (Module.finrank ℝ ℂ - 1) • f y)))
        (Ioi 0) := h3.const_mul (1/2 : ℝ)
    refine h5.congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; ring
  have hint : Integrable (fun w : ℂ => f ‖w‖) :=
    (integrable_fun_norm_addHaar (volume : Measure ℂ) (f := f)).mpr h4
  refine ⟨hint, ?_⟩
  show ∫ w : ℂ, f ‖w‖ = _
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  have hsub := integral_comp_rpow_Ioi g (two_ne_zero : (2:ℝ) ≠ 0)
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul] at hsub
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) f, hball, hdim]
  have : ∫ y in Ioi (0:ℝ), y ^ (2 - 1) • f y = (∫ t in Ioi (0:ℝ), g t) / 2 := by
    rw [← hsub, hdim]; ring
  rw [this, hV]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring
end GroundTheory.Heights₂.Heights
