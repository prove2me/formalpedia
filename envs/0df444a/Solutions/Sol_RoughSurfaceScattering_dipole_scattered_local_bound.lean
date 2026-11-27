-- Prove2me | solution 1 for RoughSurfaceScattering.dipole_scattered_local_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T03:10:44.709262+00:00
-- url     : https://prove2.me/submissions/023b76fb-0c92-4d9e-9967-bcac3a639670
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_dipole_field_joint_continuous
import Theorems.Thm_RoughSurfaceScattering_tsp_unique_upper
import Theorems.Thm_RoughSurfaceScattering_dipole_tsp_exists

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (x0 : R2) (hx0 : x0 ∈ Dplus f) (ν : R2) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ z ∈ Metric.ball x0 r, ∀ u : (R2 → ℂ) × (R2 → ℂ),
      IsTSPSolution f kp km μ (incData f (dipoleSource kp z ν)).1
        (incData f (dipoleSource kp z ν)).2 u.1 u.2 →
      ∀ x ∈ Metric.ball x0 r, ‖u.1 x‖ ≤ C ∧ ‖fderiv ℝ u.1 x‖ ≤ C := by
  classical
  have hO : IsOpen (Dplus f) := isOpen_lt (hf.1.continuous.comp (by fun_prop)) (by fun_prop)
  obtain ⟨R0, hR0, hR0s⟩ := Metric.isOpen_iff.mp hO x0 hx0
  set V : R2 → (R2 → ℂ) × (R2 → ℂ) := fun z =>
    if h : z ∈ Dplus f then Classical.choose (dipole_tsp_exists f hf kp km μ hpar z h ν)
    else (0, 0) with hVdef
  have hV : ∀ z ∈ Dplus f, IsTSPSolution f kp km μ (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 (V z).1 (V z).2 := fun z hz => by
    simp only [V, dif_pos hz]
    exact Classical.choose_spec (dipole_tsp_exists f hf kp km μ hpar z hz ν)
  obtain ⟨r, hr, h1, h2⟩ := dipole_field_joint_continuous f hf kp km μ hpar ν V hV x0 hx0
  set r' := min r (R0 / 2)
  have hr' : 0 < r' := lt_min hr (by linarith)
  have hsub : closedBall x0 r' ×ˢ closedBall x0 r' ⊆ closedBall x0 r ×ˢ closedBall x0 r :=
    Set.prod_mono (closedBall_subset_closedBall (min_le_left _ _))
      (closedBall_subset_closedBall (min_le_left _ _))
  have hK : IsCompact (closedBall x0 r' ×ˢ closedBall x0 r') :=
    (isCompact_closedBall x0 r').prod (isCompact_closedBall x0 r')
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn (h1.mono hsub)
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn (h2.mono hsub)
  have hballD : ball x0 r' ⊆ Dplus f := fun x hx =>
    hR0s (ball_subset_ball (le_trans (min_le_right _ _) (by linarith)) hx)
  refine ⟨r', hr', max M1 M2, fun z hz u hu x hx => ?_⟩
  have hzD := hballD hz
  have hxD := hballD hx
  have heq : ∀ w ∈ Dplus f, u.1 w = (V z).1 w :=
    tsp_unique_upper f hf kp km μ hpar _ _ _ _ _ _ hu (hV z hzD)
  have hev : u.1 =ᶠ[𝓝 x] (V z).1 := by
    filter_upwards [hO.mem_nhds hxD] with w hw
    exact heq w hw
  have hp : (x, z) ∈ closedBall x0 r' ×ˢ closedBall x0 r' :=
    ⟨ball_subset_closedBall hx, ball_subset_closedBall hz⟩
  rw [heq x hxD, hev.fderiv_eq]
  exact ⟨(hM1 _ hp).trans (le_max_left _ _), (hM2 _ hp).trans (le_max_right _ _)⟩
