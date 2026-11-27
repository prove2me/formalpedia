-- Prove2me | solution 1 for P2M_PositivityTheory_ThKR_lie__dc6ea91cf961
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:13:05.323388+00:00
-- url     : https://prove2.me/submissions/3e922378-1338-468c-9eab-2a94fc95f779

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_ExistsSmoothFun
import Theorems.Thm_PositivityTheory_ThKR_exists_sp
import Theorems.Thm_PositivityTheory_ThKR_exists_smooth_fun
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_scalar
import Theorems.Thm_PositivityTheory_ThKF_E_exists_ne_zero
import Theorems.Thm_PositivityTheory_ThKF_E_quad_mem


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
theorem _root_.solution (hL : PositivityTheory.ThKR.LocalLift) (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hS : ∀ t, Impl (s t) (S t))
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) :
    ∃ Q ∈ weylAlg l, ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (S t f)) (lam (Q f)) 0 := by
  obtain ⟨X, hsp, hs⟩ := exists_sp s sc s0 sm ss
  obtain ⟨ε, V, W, a, hε, V0, Vi, -, Vd⟩ := hL l X hsp
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have hφ0 : φ ≠ 0 := fun h => hφ (by simp [h])
  have hc : ∀ t, |t| < ε → ∃ c : ℂ, ∀ f, S t f = c • V t f := fun t ht => by
    obtain ⟨h1, h2, h3⟩ := Vi t ht
    have hi : Impl id (S (-t) ∘ₗ (V t).toLinearMap) := ⟨fun f => ((hS (-t)).norm _).trans (h3.norm f), fun w f g hg => by
      have := (hS (-t)).impl _ _ _ (h3.impl w f g hg)
      rw [← hs, ← sm, neg_add_cancel, s0] at this
      exact this⟩
    obtain ⟨c, hc⟩ := hi.scalar fun f => ⟨W t (S t f), by
      show S (-t) (V t (W t _)) = f
      rw [h1, ← Sm, neg_add_cancel, S0]⟩
    have h4 : ∀ f, V t f = c • S t f := fun f => by
      rw [← map_smul, ← hc]
      show _ = S t (S (-t) (V t f))
      rw [← Sm, add_neg_cancel, S0]
    have h5 : c ≠ 0 := fun h => hφ0 (by rw [← h2 φ, h4, h, zero_smul, map_zero])
    exact ⟨c⁻¹, fun f => by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩
  obtain ⟨mu, hmu, md⟩ := exists_smooth_fun S (fun t => (hS t).norm) S0 Sm Sc hφ0
  have hV0 : mu (V 0 φ) ≠ 0 := by rwa [V0]
  let c : ℝ → ℂ := fun t => mu (S t φ) / mu (V t φ)
  have cd : DifferentiableAt ℝ c 0 := md.div (Vd φ mu).differentiableAt hV0
  have c0 : c 0 = 1 := by simp only [c, S0, V0]; exact div_self hmu
  have ev : ∀ᶠ t in nhds (0 : ℝ), ∀ f, S t f = c t • V t f := by
    have e1 : ∀ᶠ t in nhds (0 : ℝ), |t| < ε := continuous_abs.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    filter_upwards [e1, (Vd φ mu).continuousAt.eventually_ne hV0] with t ht hne f
    obtain ⟨b, hb⟩ := hc t ht
    have : c t = b := by
      simp only [c, hb, map_smul, smul_eq_mul]
      exact mul_div_cancel_right₀ _ hne
    rw [this, hb]
  refine ⟨(deriv c 0 + a) • 1 + quad X, add_mem (Subalgebra.smul_mem _ (one_mem _) _) (quad_mem X), fun f lam => ?_⟩
  refine ((cd.hasDerivAt.fun_mul (Vd f lam)).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp [c0, V0]
    ring
  · filter_upwards [ev] with t ht
    rw [ht, map_smul, smul_eq_mul]
end PositivityTheory.ThKR
