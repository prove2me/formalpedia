-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdChar.eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:10.524926+00:00
-- url     : https://prove2.me/submissions/b55843a4-9ede-4344-a4ef-4d3b7fb04c95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdChar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
namespace PI.OmFibreUniq.W.SdChar
theorem _root_.solution (w : ℂ) (hw : ‖w‖ = 1) (h : ∀ m : ℕ, ‖w ^ m - 1‖ < 1) : w = 1 := by
  have key : ∀ y : ℝ, Real.cos y ≤ 1 / 2 → 1 ≤ ‖Complex.exp (y * Complex.I) - 1‖ := by
    intro y hy
    have hsq : ‖Complex.exp (y * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos y := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im]
      nlinarith [Real.sin_sq_add_cos_sq y]
    nlinarith [norm_nonneg (Complex.exp (y * Complex.I) - 1)]
  set θ := Complex.arg w with hθ
  have hw' : w = Complex.exp (θ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at this
    simpa using this.symm
  have hpow : ∀ m : ℕ, w ^ m = Complex.exp (((m : ℝ) * θ : ℝ) * Complex.I) := by
    intro m
    rw [hw', ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  by_contra hne
  have hθ0 : θ ≠ 0 := by
    intro h0
    apply hne
    rw [hw', h0]
    simp
  have hθb : -Real.pi < θ ∧ θ ≤ Real.pi := ⟨Complex.neg_pi_lt_arg w, Complex.arg_le_pi w⟩
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, Real.pi / 3 ≤ m * |θ| ∧ m * |θ| ≤ Real.pi := by
    have ht : 0 < |θ| := abs_pos.mpr hθ0
    have ht' : |θ| ≤ Real.pi := abs_le.mpr ⟨by linarith [hθb.1], hθb.2⟩
    by_cases hbig : Real.pi / 3 ≤ |θ|
    · exact ⟨1, by simpa using hbig, by simpa using ht'⟩
    · push_neg at hbig
      refine ⟨⌈Real.pi / 3 / |θ|⌉₊, ?_, ?_⟩
      · have := Nat.le_ceil (Real.pi / 3 / |θ|)
        rw [div_le_iff₀ ht] at this
        linarith
      · have h1 := Nat.ceil_lt_add_one (show 0 ≤ Real.pi / 3 / |θ| by positivity)
        have h2 : (⌈Real.pi / 3 / |θ|⌉₊ : ℝ) * |θ| < (Real.pi / 3 / |θ| + 1) * |θ| :=
          mul_lt_mul_of_pos_right h1 ht
        rw [add_mul, div_mul_cancel₀ _ ht.ne'] at h2
        linarith [Real.pi_pos]
  have hcos : Real.cos ((m : ℝ) * θ) ≤ 1 / 2 := by
    have e : Real.cos ((m : ℝ) * θ) = Real.cos ((m : ℝ) * |θ|) := by
      rcases abs_choice θ with h | h <;> rw [h] <;> simp [mul_neg, Real.cos_neg]
    rw [e, ← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hm2 hm1
  have := h m
  rw [hpow m] at this
  linarith [key _ hcos]
end PI.OmFibreUniq.W.SdChar
