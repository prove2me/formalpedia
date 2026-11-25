-- Prove2me | solution 1 for PositivityTheory.RL.Delta.eq_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:17.661163+00:00
-- url     : https://prove2.me/submissions/ebf6877a-9cc6-4ec1-8e4a-bcd259df7662

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD
import Theorems.Thm_PositivityTheory_RL_Delta_dense_hasCompactSupport
import Theorems.Thm_PositivityTheory_RL_Delta_zero_of_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Delta
open Complex
open scoped Real ContDiff
namespace PositivityTheory.RL.Delta
theorem _root_.solution (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (t : ℝ) (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ),
      (∀ x, g x = cexp (2 * π * I * (t * x i : ℝ)) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * f 0 := by
  have hA : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, HasCompactSupport (f : (Fin n → ℝ) → ℂ) → f 0 = 0 → T f = 0 := by
    intro f hf h0
    obtain ⟨R, hR, hs⟩ := hf.isCompact.isBounded.subset_ball_lt 0 0
    let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
    have he : ∀ x, e x = R • x := fun _ => rfl
    have he' : ∀ x, e.symm x = R⁻¹ • x := fun x => e.injective (by rw [e.apply_symm_apply, he, smul_inv_smul₀ hR.ne'])
    have := zero_of_ball n (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
      (fun i f g h => hχ R⁻¹ i _ _ fun x => by
        show g (e.symm x) = _ * f (e.symm x)
        rw [h, he']; simp) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ?_ (by
        show f (e 0) = 0
        rw [map_zero, h0])
    · rw [← this]
      exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.apply_symm_apply x).symm)
    · have hsub : Function.support (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ⊆ e ⁻¹' tsupport f :=
        fun x hx => subset_tsupport _ hx
      refine (closure_minimal hsub ((isClosed_tsupport _).preimage e.continuous)).trans fun x hx => ?_
      have := hs hx
      rw [mem_ball_zero_iff, he, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at this
      rw [mem_ball_zero_iff]
      exact (mul_lt_iff_lt_one_right hR).1 this
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) :=
    b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ :=
    h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  refine ⟨T ψ, fun f => ?_⟩
  let S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _
  have hcl : IsClosed {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f} :=
    isClosed_eq T.continuous (continuous_const.mul S.continuous)
  refine closure_minimal (t := {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f}) ?_ hcl (dense_hasCompactSupport n f)
  intro f hf
  have := hA (f - f 0 • ψ) (HasCompactSupport.sub hf (HasCompactSupport.smul_left (f := fun _ => f 0) h₁)) (by
    show f 0 - f 0 • ψ 0 = 0
    rw [hψ0]; simp)
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul, mul_comm] at this
  exact this
end PositivityTheory.RL.Delta
