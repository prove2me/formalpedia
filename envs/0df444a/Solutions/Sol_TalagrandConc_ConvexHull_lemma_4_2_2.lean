-- Prove2me | solution 1 for TalagrandConc.ConvexHull.lemma_4_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:44:57.436126+00:00
-- url     : https://prove2.me/submissions/e945ef2e-179b-459a-bb13-3de0b0a6d0d7

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic



namespace TalagrandConc.ConvexHull

/-- The derivative of `ξ(α, ·)` on `(0,1)`. -/
noncomputable def xiD (α u : ℝ) : ℝ :=
  α * (Real.log (1 + α - α * u) - Real.log (1 - u) - Real.log (1 + α))

lemma xi_hasDerivAt (α : ℝ) (hα : 0 < α) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (xi α) (xiD α u) u := by
  have h1u : 0 < 1 - u := by linarith
  have h1α : 0 < 1 + α := by linarith
  have hq : 0 < 1 + α - α * u := by nlinarith
  have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := (hasDerivAt_id' u).const_sub 1
  have h2 : HasDerivAt (fun u : ℝ => Real.log (1 - u)) ((-1) / (1 - u)) u :=
    h1.log h1u.ne'
  have h3 : HasDerivAt (fun u : ℝ => α * (1 - u)) (α * (-1)) u := h1.const_mul α
  have h4 := h3.mul h2
  have h5 : HasDerivAt (fun u : ℝ => 1 + α - α * u) (-(α * 1)) u :=
    ((hasDerivAt_id' u).const_mul α).const_sub (1 + α)
  have h6 : HasDerivAt (fun u : ℝ => (1 + α - α * u) / (1 + α)) ((-(α * 1)) / (1 + α)) u :=
    h5.div_const (1 + α)
  have h7 : HasDerivAt (fun u : ℝ => Real.log ((1 + α - α * u) / (1 + α)))
      (((-(α * 1)) / (1 + α)) / ((1 + α - α * u) / (1 + α))) u :=
    h6.log (by positivity)
  have h8 : HasDerivAt (fun u : ℝ => α + 1 - α * u) (-(α * 1)) u :=
    ((hasDerivAt_id' u).const_mul α).const_sub (α + 1)
  have h9 := h8.mul h7
  have h10 := h4.sub h9
  unfold xi
  refine h10.congr_deriv ?_
  unfold xiD
  rw [Real.log_div hq.ne' h1α.ne']
  field_simp
  ring

lemma xi_continuousOn (α : ℝ) (hα : 0 < α) : ContinuousOn (xi α) (Set.Icc 0 1) := by
  have e : xi α = fun u => α * ((1 - u) * Real.log (1 - u)) -
      (α + 1 - α * u) * Real.log ((1 + α - α * u) / (1 + α)) := by
    funext u; unfold xi; ring
  rw [e]
  apply ContinuousOn.sub
  · exact (continuous_const.mul
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).continuousOn
  · apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    have : 0 < 1 + α - α * x := by nlinarith [hx.2]
    positivity

lemma xiD_pos (α : ℝ) (hα : 0 < α) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : 0 < xiD α u := by
  unfold xiD
  have h1u : 0 < 1 - u := by linarith
  have h1α : 0 < 1 + α := by linarith
  have hq : 0 < 1 + α - α * u := by nlinarith
  have : Real.log ((1 - u) * (1 + α)) < Real.log (1 + α - α * u) := by
    apply Real.log_lt_log (by positivity)
    nlinarith
  rw [Real.log_mul h1u.ne' h1α.ne'] at this
  have : 0 < Real.log (1 + α - α * u) - Real.log (1 - u) - Real.log (1 + α) := by linarith
  positivity

lemma xiD_mono (α : ℝ) (hα : 0 < α) : MonotoneOn (xiD α) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  unfold xiD
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have h1y : 0 < 1 - y := by linarith [hy.2]
  have hqx : 0 < 1 + α - α * x := by nlinarith [hx.2]
  have hqy : 0 < 1 + α - α * y := by nlinarith [hy.2]
  have key : Real.log ((1 + α - α * x) / (1 - x)) ≤ Real.log ((1 + α - α * y) / (1 - y)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ h1x h1y]
    nlinarith
  rw [Real.log_div hqx.ne' h1x.ne', Real.log_div hqy.ne' h1y.ne'] at key
  have : Real.log (1 + α - α * x) - Real.log (1 - x) - Real.log (1 + α) ≤
      Real.log (1 + α - α * y) - Real.log (1 - y) - Real.log (1 + α) := by linarith
  exact mul_le_mul_of_nonneg_left this hα.le

lemma xi_strictMono (α : ℝ) (hα : 0 < α) : StrictMonoOn (xi α) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (xi_continuousOn α hα)
  intro x hx
  rw [interior_Icc] at hx
  rw [(xi_hasDerivAt α hα x hx.1 hx.2).deriv]
  exact xiD_pos α hα x hx.1 hx.2

lemma xi_convex (α : ℝ) (hα : 0 < α) : ConvexOn ℝ (Set.Icc 0 1) (xi α) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1) (xi_continuousOn α hα)
  · rw [interior_Icc]
    intro x hx
    exact (xi_hasDerivAt α hα x hx.1 hx.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(xi_hasDerivAt α hα x hx.1 hx.2).deriv, (xi_hasDerivAt α hα y hy.1 hy.2).deriv]
    exact xiD_mono α hα hx hy hxy

lemma xi_zero (α : ℝ) (hα : 0 < α) : xi α 0 = 0 := by
  unfold xi
  have : (1 + α - α * 0) / (1 + α) = 1 := by
    rw [mul_zero, sub_zero]; exact div_self (by linarith)
  rw [this]
  simp

lemma xi_lower (α : ℝ) (hα : 0 < α) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, α / (2 * (α + 1)) * u ^ 2 ≤ xi α u := by
  set c : ℝ := α / (2 * (α + 1)) with hc
  have hcpos : 0 < c := by positivity
  let h : ℝ → ℝ := fun u => xi α u - c * u ^ 2
  have hmono : MonotoneOn h (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (xi_continuousOn α hα).sub (by fun_prop)
    · rw [interior_Icc]
      intro x hx
      exact ((xi_hasDerivAt α hα x hx.1 hx.2).sub
        (((hasDerivAt_pow 2 x).const_mul c))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hd : HasDerivAt h (xiD α x - c * (↑(2 : ℕ) * x ^ (2 - 1))) x :=
        (xi_hasDerivAt α hα x hx.1 hx.2).sub ((hasDerivAt_pow 2 x).const_mul c)
      rw [hd.deriv]
      -- xiD α x ≥ α x / (1 + α) ≥ c * 2 x
      have h1x : 0 < 1 - x := by linarith [hx.2]
      have h1α : 0 < 1 + α := by linarith
      have hqx : 0 < 1 + α - α * x := by nlinarith [hx.2]
      have hlog : 1 - ((1 - x) * (1 + α)) / (1 + α - α * x) ≤
          Real.log (1 + α - α * x) - Real.log (1 - x) - Real.log (1 + α) := by
        have hz : 0 < (1 + α - α * x) / ((1 - x) * (1 + α)) := by positivity
        have := Real.one_sub_inv_le_log_of_pos hz
        rw [Real.log_div hqx.ne' (by positivity), Real.log_mul h1x.ne' h1α.ne', inv_div] at this
        linarith
      have e1 : 1 - ((1 - x) * (1 + α)) / (1 + α - α * x) = x / (1 + α - α * x) := by
        rw [eq_div_iff hqx.ne', sub_mul, div_mul_cancel₀ _ hqx.ne']
        ring
      rw [e1] at hlog
      have h2 : x / (1 + α) ≤ x / (1 + α - α * x) := by
        apply div_le_div_of_nonneg_left hx.1.le hqx
        nlinarith [hx.1]
      have h3 : xiD α x ≥ α * (x / (1 + α)) := by
        unfold xiD
        exact mul_le_mul_of_nonneg_left (h2.trans hlog) hα.le
      have h4 : c * (↑(2 : ℕ) * x ^ (2 - 1)) = α * (x / (1 + α)) := by
        rw [hc]
        field_simp
        ring
      rw [h4]
      linarith
  intro u hu
  have := hmono ⟨le_rfl, zero_le_one⟩ hu hu.1
  simp only [h, xi_zero α hα] at this
  linarith

lemma lemma_4_2_2_core (α : ℝ) (hα : 0 < α) :
    StrictMonoOn (xi α) (Set.Icc 0 1) ∧ ConvexOn ℝ (Set.Icc 0 1) (xi α) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, α / (2 * (α + 1)) * u ^ 2 ≤ xi α u :=
  ⟨xi_strictMono α hα, xi_convex α hα, xi_lower α hα⟩

end TalagrandConc.ConvexHull

open TalagrandConc.ConvexHull


theorem solution (α : ℝ) (hα : 0 < α) :
    StrictMonoOn (xi α) (Set.Icc 0 1) ∧ ConvexOn ℝ (Set.Icc 0 1) (xi α) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, α / (2 * (α + 1)) * u ^ 2 ≤ xi α u := by
  exact lemma_4_2_2_core α hα
