-- Prove2me | solution 1 for PI.EF.Loc.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:49:56.469808+00:00
-- url     : https://prove2.me/submissions/69394f03-88ed-4eed-ae9a-b725c2004984

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBoundOfZeroFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalAbstract
import Theorems.Thm_PI_EF_Loc_gfun_bounds
import Theorems.Thm_PI_EF_Loc_differentiable_refl
import Theorems.Thm_PI_EF_Loc_le_norm_refl
import Theorems.Thm_PI_EF_Loc_logDeriv_bound_of_zero_free
import Theorems.Thm_PI_EF_Loc_logDeriv_prod_pow_mul
import Theorems.Thm_PI_EF_Loc_norm_logDeriv_refl_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.EF.Loc
open Complex Metric Set Filter Topology
section core
variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}
private theorem differentiableOn_gfun_of_differentiableOn {U : Set ℂ} (hh : DifferentiableOn ℂ h U) :
    DifferentiableOn ℂ (gfun s₀ R Z m h) U := by
  have e : gfun s₀ R Z m h = fun z => (∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) * h z := rfl
  rw [e]
  refine DifferentiableOn.mul ?_ hh
  have hd : Differentiable ℂ (fun z => ∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) := by
    first
      | exact Differentiable.finset_prod fun ρ _ => (differentiable_refl s₀ R ρ).pow (m ρ)
      | (have hbd := differentiable_refl s₀ R; fun_prop)
  exact hd.differentiableOn
end core
end PI.EF.Loc
end
end

set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology
variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}
namespace PI.EF.Loc
theorem _root_.solution (hDL : PI.DiscLog) (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) (hM : 0 < M)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
      ‖logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  intro s hs hfs
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨hg, hN⟩ := gfun_bounds hR' hR'R hZ hh hh0 hfac hb
  have hsR' : s ∈ closedBall s₀ R' := closedBall_subset_closedBall hrR'.le hs
  have hsball : s ∈ ball s₀ R := closedBall_subset_ball (hrR'.trans hR'R) hs
  have hsR : s ∈ closedBall s₀ R := ball_subset_closedBall hsball
  have hnhds : closedBall s₀ R ∈ 𝓝 s :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hsball) ball_subset_closedBall
  have hhs : h s ≠ 0 := hh0 s hsR'
  have hhd : DifferentiableAt ℂ h s := hh.differentiableAt hnhds
  have hρs : ∀ ρ ∈ Z, s - ρ ≠ 0 := by
    intro ρ hρ h0
    have hsρ : s = ρ := sub_eq_zero.mp h0
    exact hfs (by rw [hsρ]; exact ((hZ ρ).1 hρ).2)
  have hfeq : f =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem hnhds fun z hz => hfac z hz
  have hlf : logDeriv f s = (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + logDeriv h s := by
    have e1 : logDeriv f s = logDeriv (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z) s := by
      rw [logDeriv_apply, logDeriv_apply, hfeq.deriv_eq, hfeq.eq_of_nhds]
    rw [e1]
    refine (logDeriv_prod_pow_mul (φ := fun ρ z => z - ρ) (h := h) hρs
      (fun ρ _ => by fun_prop) hhs hhd).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    show (m ρ : ℂ) * logDeriv (fun z => z - ρ) s = (m ρ : ℂ) / (s - ρ)
    simp only [logDeriv_apply, deriv_sub_const, deriv_id'']
    ring
  have hBne : ∀ z ∈ closedBall s₀ R, ∀ ρ ∈ Z, refl s₀ R ρ z ≠ 0 := by
    intro z hz ρ hρ h0
    have h1 := le_norm_refl (R' := R') hR ((hZ ρ).1 hρ).1 hz
    rw [h0, norm_zero] at h1
    linarith
  have hlg : logDeriv (gfun s₀ R Z m h) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s) + logDeriv h s :=
    logDeriv_prod_pow_mul (φ := fun ρ => refl s₀ R ρ) (fun ρ hρ => hBne s hsR ρ hρ)
      (fun ρ _ => (differentiable_refl s₀ R ρ).differentiableAt) hhs hhd
  have hsub : ball s₀ R' ⊆ closedBall s₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hR'R.le)
  have hgne : ∀ z ∈ ball s₀ R', gfun s₀ R Z m h z ≠ 0 := by
    intro z hz
    simp only [gfun]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hBne z (hsub hz) ρ hρ))
      (hh0 z (ball_subset_closedBall hz))
  have hLg := logDeriv_bound_of_zero_free hDL hr hrR' hM
    (differentiableOn_gfun_of_differentiableOn (hh.mono hsub)) hgne (fun z hz => hg z (hsub hz)) s hs
  have hLg' : ‖logDeriv (gfun s₀ R Z m h) s‖ ≤ 4 * (r + R') / (R' - r) ^ 2 * M := by
    rw [logDeriv_apply]
    exact hLg
  have hK : 0 ≤ R' / (R * (R - R')) := div_nonneg hR'.le (mul_pos hR (by linarith)).le
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have hNle : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ M / Real.log (R / R') := by
    exact (le_div_iff₀ hlog).mpr hN
  have hsumB : ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ ≤
      R' / (R * (R - R')) / Real.log (R / R') * M := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (R' / (R * (R - R'))) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_mul]
          have hn : ‖(m ρ : ℂ)‖ = (m ρ : ℝ) := by
            exact Complex.norm_natCast _
          rw [hn]
          exact mul_le_mul_of_nonneg_left
            (norm_logDeriv_refl_le hR'R hR ((hZ ρ).1 hρ).1 hsR) (Nat.cast_nonneg _)
      _ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (R' / (R * (R - R'))) := by
          rw [Nat.cast_sum, Finset.sum_mul]
      _ ≤ M / Real.log (R / R') * (R' / (R * (R - R'))) :=
          mul_le_mul_of_nonneg_right hNle hK
      _ = R' / (R * (R - R')) / Real.log (R / R') * M := by ring
  have hdiff : logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) =
      logDeriv (gfun s₀ R Z m h) s -
        ∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s := by
    rw [hlf, hlg]
    ring
  rw [hdiff]
  calc _ ≤ ‖logDeriv (gfun s₀ R Z m h) s‖ +
        ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sub_le _ _
    _ ≤ 4 * (r + R') / (R' - r) ^ 2 * M + R' / (R * (R - R')) / Real.log (R / R') * M :=
        add_le_add hLg' hsumB
    _ = locC r R' R * M := by
        unfold locC
        ring
end PI.EF.Loc
