-- Prove2me | solution 1 for PositivityTheory.ThKR.exists_smooth_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:03.90557+00:00
-- url     : https://prove2.me/submissions/91124a29-9352-4147-b7dc-abd920c69fda

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_ExistsSmoothFun
import Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR
theorem _root_.solution (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hn : ∀ t f, ‖(S t f).toLp 2 volume‖ = ‖f.toLp 2 volume‖)
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) {φ : Sch l} (hφ : φ ≠ 0) :
    ∃ mu : Sch l →L[ℂ] ℂ, mu φ ≠ 0 ∧ DifferentiableAt ℝ (fun t => mu (S t φ)) 0 := by
  let lam : Sch l →L[ℂ] ℂ := (innerSL ℂ (φ.toLp 2 volume)).comp (schwartzToL2 l)
  have h2 : lam φ ≠ 0 := fun h => hφ (by
    apply injective_toLp 2 volume
    have : φ.toLp 2 volume = 0 := inner_self_eq_zero.1 h
    exact this.trans (map_zero (schwartzToL2 l)).symm)
  have hb : ∀ t f, ‖lam (S t f)‖ ≤ ‖φ.toLp 2 volume‖ * ‖schwartzToL2 l f‖ := fun t f => by
    have := norm_inner_le_norm (𝕜 := ℂ) (φ.toLp 2 volume) ((S t f).toLp 2 volume)
    rw [hn] at this
    exact this
  have hc := Sc φ lam
  have hI : ∀ t, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, lam (S s φ)) (lam (S t φ)) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, lam (S s φ)) ≠ 0 := by
    by_contra h
    push Not at h
    have h3 := hI 0
    simp only [h, S0] at h3
    exact h2 (h3.unique (hasDerivAt_const _ _))
  let m : Sch l →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ s in (0 : ℝ)..δ, lam (S s f)
      map_add' := fun f g => by
        simp only [map_add]
        exact intervalIntegral.integral_add ((Sc f lam).intervalIntegrable _ _) ((Sc g lam).intervalIntegrable _ _)
      map_smul' := fun a f => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul _ _ }
  have mc : Continuous m := by
    refine continuous_of_continuousAt_zero m ?_
    rw [ContinuousAt, map_zero]
    have h0 : Continuous fun f : Sch l => ‖φ.toLp 2 volume‖ * ‖schwartzToL2 l f‖ * |δ - 0| := by fun_prop
    have h1 := h0.tendsto 0
    simp only [map_zero, norm_zero, mul_zero, zero_mul] at h1
    exact squeeze_zero_norm (fun f => intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hb s f) h1
  refine ⟨⟨m, mc⟩, hδ, ?_⟩
  have key : ∀ t, m (S t φ) = (∫ s in (0 : ℝ)..(δ + t), lam (S s φ)) - ∫ s in (0 : ℝ)..t, lam (S s φ) := fun t => by
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have := intervalIntegral.integral_comp_add_right (fun s => lam (S s φ)) (a := 0) (b := δ) t
    rw [zero_add] at this
    rw [← this]
    simp only [Sm]
    rfl
  show DifferentiableAt ℝ (fun t => m (S t φ)) 0
  simp only [key]
  exact (((hI (δ + 0)).comp_const_add δ 0).sub (hI 0)).differentiableAt
end PositivityTheory.ThKR
