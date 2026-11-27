-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PuncturedExpOrder_proof_da882b5a154f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:50.333451+00:00
-- url     : https://prove2.me/submissions/88a34a73-b947-428d-acca-15544d68fca9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPuncturedExpOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace PuncturedExpOrder
theorem _root_.solution : PuncturedExpOrder.Statement := by
  intro R ψ k M hR hψ hb
  have hSo : IsOpen (ball (0 : ℂ) R \ {0}) := isOpen_ball.sdiff isClosed_singleton
  set F : ℂ → ℂ := fun x => Complex.exp (ψ x) * x ^ k with hFdef
  have hFd : DifferentiableOn ℂ F (ball (0 : ℂ) R \ {0}) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.2
    have h1 : DifferentiableAt ℂ ψ x := (hψ x hx).differentiableAt (hSo.mem_nhds hx)
    exact (h1.cexp.mul ((hasDerivAt_zpow k x (Or.inl hx0)).differentiableAt)).differentiableWithinAt
  have hFb : BddAbove (norm ∘ F '' (ball (0 : ℂ) R \ {0})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hb x hx
  set G : ℂ → ℂ := Function.update F 0 (limUnder (𝓝[≠] (0 : ℂ)) F) with hGdef
  have hGd : DifferentiableOn ℂ G (ball (0 : ℂ) R) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hR) hFd hFb
  have hGa : AnalyticAt ℂ G 0 := hGd.analyticAt (ball_mem_nhds 0 hR)
  have hGF : ∀ x : ℂ, x ≠ 0 → G x = F x := fun x hx => Function.update_of_ne hx _ _
  have hnz : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), G z = 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {(0 : ℂ)}ᶜ ∈ 𝓝[≠] (0 : ℂ))).exists
    have hx0' : x ≠ 0 := hx0
    rw [hGF x hx0', hFdef] at hx
    exact mul_ne_zero (Complex.exp_ne_zero _) (zpow_ne_zero _ hx0') hx
  obtain ⟨m, u, hua, hu0, hGu⟩ := hGa.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hev : ∀ᶠ x in 𝓝 (0 : ℂ),
      AnalyticAt ℂ u x ∧ u x ≠ 0 ∧ G x = x ^ m * u x ∧ x ∈ ball (0 : ℂ) R := by
    filter_upwards [hua.eventually_analyticAt, hua.continuousAt.eventually_ne hu0, hGu,
      ball_mem_nhds (0 : ℂ) hR] with x h1 h2 h3 h4
    exact ⟨h1, h2, by simpa using h3, h4⟩
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set j : ℤ := (m : ℤ) - k with hjdef

  have hkey : ∀ x ∈ ball (0 : ℂ) ε, x ≠ 0 → Complex.exp (ψ x) = x ^ j * u x := by
    intro x hx hx0
    obtain ⟨-, -, h3, -⟩ := hεs x hx
    rw [hGF x hx0, hFdef] at h3
    have hk : x ^ k ≠ 0 := zpow_ne_zero _ hx0
    rw [hjdef, zpow_sub₀ hx0, zpow_natCast, div_mul_eq_mul_div, ← h3,
      mul_div_cancel_right₀ _ hk]
  have hSε : IsOpen (ball (0 : ℂ) ε \ {0}) := isOpen_ball.sdiff isClosed_singleton

  have hlog : ∀ x ∈ ball (0 : ℂ) ε, x ≠ 0 →
      HasDerivAt ψ (deriv ψ x) x ∧ deriv ψ x = (j : ℂ) * (x - 0)⁻¹ + deriv u x / u x := by
    intro x hx hx0
    obtain ⟨hux, hu0x, -, hxR⟩ := hεs x hx
    have hψx : HasDerivAt ψ (deriv ψ x) x :=
      ((hψ x ⟨hxR, hx0⟩).differentiableAt (hSo.mem_nhds ⟨hxR, hx0⟩)).hasDerivAt
    refine ⟨hψx, ?_⟩
    have h1 : HasDerivAt (fun y => Complex.exp (ψ y)) (Complex.exp (ψ x) * deriv ψ x) x :=
      hψx.cexp
    have h2 : HasDerivAt (fun y => y ^ j * u y)
        ((j : ℂ) * x ^ (j - 1) * u x + x ^ j * deriv u x) x :=
      (hasDerivAt_zpow j x (Or.inl hx0)).mul hux.differentiableAt.hasDerivAt
    have heq : (fun y => Complex.exp (ψ y)) =ᶠ[𝓝 x] fun y => y ^ j * u y := by
      filter_upwards [hSε.mem_nhds ⟨hx, hx0⟩] with y hy
      exact hkey y hy.1 hy.2
    have h3 := (h1.congr_of_eventuallyEq heq.symm).unique h2
    rw [hkey x hx hx0, zpow_sub_one₀ hx0] at h3
    have hxj : x ^ j ≠ 0 := zpow_ne_zero _ hx0
    have hd : deriv ψ x =
        ((j : ℂ) * (x ^ j * x⁻¹) * u x + x ^ j * deriv u x) / (x ^ j * u x) := by
      rw [eq_div_iff (mul_ne_zero hxj hu0x)]
      linear_combination h3
    rw [hd, sub_zero]
    field_simp

  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := half_pos hε
  have hsph : ∀ z ∈ sphere (0 : ℂ) r, z ∈ ball (0 : ℂ) ε ∧ z ≠ 0 := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa using hz
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, hz']
      exact half_lt_self hε
    · intro h
      rw [h, norm_zero] at hz'
      exact hr.ne hz'
  have hudiff : DifferentiableOn ℂ (fun z => deriv u z / u z) (ball (0 : ℂ) ε) := by
    intro z hz
    obtain ⟨huz, hu0z, -, -⟩ := hεs z hz
    exact (huz.deriv.differentiableAt.div huz.differentiableAt hu0z).differentiableWithinAt
  have hI1 : (∮ z in C(0, r), deriv ψ z) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.le fun z hz =>
      (hlog z (hsph z hz).1 (hsph z hz).2).1.hasDerivWithinAt
  have hI2 : (∮ z in C(0, r), deriv ψ z) =
      ∮ z in C(0, r), ((j : ℂ) * (z - 0)⁻¹ + deriv u z / u z) :=
    circleIntegral.integral_congr hr.le fun z hz => (hlog z (hsph z hz).1 (hsph z hz).2).2
  have hc1 : CircleIntegrable (fun z : ℂ => (j : ℂ) * (z - 0)⁻¹) 0 r := by
    refine ContinuousOn.circleIntegrable hr.le ?_
    refine continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ ?_)
    intro z hz
    simpa using (hsph z hz).2
  have hc2 : CircleIntegrable (fun z : ℂ => deriv u z / u z) 0 r :=
    ContinuousOn.circleIntegrable hr.le (hudiff.continuousOn.mono fun z hz => (hsph z hz).1)
  have hI3 : (∮ z in C(0, r), deriv u z / u z) = 0 := by
    refine DiffContOnCl.circleIntegral_eq_zero hr.le (DifferentiableOn.diffContOnCl ?_)
    rw [closure_ball (0 : ℂ) hr.ne']
    exact hudiff.mono (closedBall_subset_ball (half_lt_self hε))
  have hI4 : (∮ z in C(0, r), (j : ℂ) * (z - 0)⁻¹) = (j : ℂ) * (2 * π * Complex.I) := by
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv 0 hr.ne']
  rw [circleIntegral.integral_add hc1 hc2, hI3, hI4, add_zero] at hI2
  rw [hI1] at hI2
  have hj0 : (j : ℂ) = 0 := by
    rcases mul_eq_zero.mp hI2.symm with h | h
    · exact h
    · exact absurd h Complex.two_pi_I_ne_zero
  have hj : j = 0 := by exact_mod_cast hj0
  refine ⟨?_, u 0, hu0, ?_⟩
  · have : (m : ℤ) - k = 0 := hj
    omega
  · refine (hua.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [inter_mem_nhdsWithin ({(0 : ℂ)}ᶜ) (ball_mem_nhds (0 : ℂ) hε)] with x hx
    rw [hkey x hx.2 hx.1, hj, zpow_zero, one_mul]
end PuncturedExpOrder
end GroundTheory.Heights₂.Heights.Regular
