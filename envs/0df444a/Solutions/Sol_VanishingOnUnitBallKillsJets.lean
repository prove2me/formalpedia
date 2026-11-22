-- Prove2me | solution 1 for VanishingOnUnitBallKillsJets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:15:29.428072+00:00
-- url     : https://prove2.me/submissions/4aed6807-fc4d-4519-b9cc-03ce45b0f578

import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_VanishingOnUnitBallKillsJets
import Theorems.Thm_IteratedDerivAlongRay


set_option autoImplicit false

theorem _root_.solution (S : Plane → ℝ) (hS : ContDiff ℝ (⊤ : ℕ∞) S)
    (hvan : ∀ w : Plane, ‖w‖ ≤ 1 → S w = 0) :
    ∀ (j : ℕ) (w : Plane), iteratedFDeriv ℝ j S 0 (fun _ => w) = 0 := by
  -- DIRECTIONS IN THE CLOSED UNIT BALL.  Restrict `S` to the ray through `w` and use locality
  -- in one variable, then transfer back along the ray.
  have hsmall : ∀ (j : ℕ) (w : Plane), ‖w‖ ≤ 1 →
      iteratedFDeriv ℝ j S 0 (fun _ => w) = 0 := by
    intro j w hw
    have hray := IteratedDerivAlongRay Set.univ isOpen_univ S j
      (hS.contDiffOn.of_le (by exact_mod_cast le_top)) 0 w 0 (Set.mem_univ _)
    rw [zero_smul, add_zero] at hray
    rw [← hray]
    -- the restriction vanishes on `(-1,1)`, hence agrees with `0` near `0`
    have hev : (fun s : ℝ => S ((0 : Plane) + s • w)) =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      refine hvan ((0 : Plane) + s • w) ?_
      rw [zero_add, norm_smul, Real.norm_eq_abs]
      calc |s| * ‖w‖ ≤ |s| * 1 := mul_le_mul_of_nonneg_left hw (abs_nonneg s)
        _ = |s| := by ring
        _ ≤ 1 := le_of_lt hs
    rw [iteratedDeriv_eq_iteratedFDeriv, (hev.iteratedFDeriv ℝ j).self_of_nhds]
    simp
  -- EVERY DIRECTION, by positive homogeneity of a diagonal evaluation.
  intro j w
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · exact hsmall j w hw
  · obtain ⟨τ, hτdef⟩ : ∃ t : ℝ, t = ‖w‖ := ⟨_, rfl⟩
    have hτ0 : 0 < τ := by rw [hτdef]; linarith
    have hτne : τ ≠ 0 := ne_of_gt hτ0
    have hwe : w = τ • (τ⁻¹ • w) := by
      rw [smul_smul, mul_inv_cancel₀ hτne, one_smul]
    have hw'eq : ‖τ⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ0), ← hτdef,
        inv_mul_cancel₀ hτne]
    have hhom : ∀ (Q : ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) ℝ) (c : ℝ)
        (x : Plane), Q (fun _ => c • x) = c ^ j * Q (fun _ => x) := by
      intro Q c x
      rw [show (fun _ : Fin j => c • x)
          = fun i : Fin j => (fun _ : Fin j => c) i • (fun _ : Fin j => x) i from rfl,
        Q.map_smul_univ]
      simp [Finset.prod_const]
    have hkey : iteratedFDeriv ℝ j S 0 (fun _ => w)
        = τ ^ j * iteratedFDeriv ℝ j S 0 (fun _ => τ⁻¹ • w) := by
      conv_lhs => rw [hwe]
      exact hhom (iteratedFDeriv ℝ j S 0) τ (τ⁻¹ • w)
    rw [hkey, hsmall j (τ⁻¹ • w) (le_of_eq hw'eq), mul_zero]
