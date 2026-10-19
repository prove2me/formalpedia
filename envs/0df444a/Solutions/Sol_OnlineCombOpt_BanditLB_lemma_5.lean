-- Prove2me | solution 1 for OnlineCombOpt.BanditLB.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:00:37.179974+00:00
-- url     : https://prove2.me/submissions/aff2c096-2066-4a2f-af07-b6d27fafc4d3

import Mathlib
set_option autoImplicit false

theorem solution (x₀ x : ℝ) (hx₀ : 0 < x₀) (hx₀one : x₀ < 1)
    (hxx₀ : x₀ ≤ x) :
    -Real.log x ≤ -(x - 1) + (x - 1)^2 / (2 * x₀) := by
  have hx : 0 < x := lt_of_lt_of_le hx₀ hxx₀
  rcases le_or_gt 1 x with h1 | h1
  · -- x ≥ 1
    have key : ∀ y : ℝ, 1 ≤ y → 0 ≤ Real.log y - (y - 1) + (y - 1)^2 / 2 := by
      have hmono : MonotoneOn (fun y : ℝ => Real.log y - (y - 1) + (y - 1)^2 / 2) (Set.Ici 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
        · apply ContinuousOn.add
          · apply ContinuousOn.sub
            · exact Real.continuousOn_log.mono (fun y hy => by simp at hy ⊢; linarith)
            · fun_prop
          · fun_prop
        · intro y hy
          have hy' : 0 < y := by simp at hy; linarith
          have : DifferentiableAt ℝ (fun y : ℝ => Real.log y - (y - 1) + (y - 1)^2 / 2) y := by
            have := Real.differentiableAt_log hy'.ne'
            fun_prop (disch := exact hy'.ne')
          exact this.differentiableWithinAt
        · intro y hy
          have hy' : 1 < y := by simpa using hy
          have hy0 : 0 < y := by linarith
          have hd : HasDerivAt (fun y : ℝ => Real.log y - (y - 1) + (y - 1)^2 / 2) (y⁻¹ - 1 + (y - 1)) y := by
            have h1 := Real.hasDerivAt_log hy0.ne'
            have h2 : HasDerivAt (fun y : ℝ => (y - 1)) 1 y := (hasDerivAt_id y).sub_const 1
            have h3 : HasDerivAt (fun y : ℝ => (y - 1)^2 / 2) ((2 * (y-1)^1 * 1) / 2) y := by
              have := (h2.pow 2).div_const 2
              simpa using this
            exact ((h1.sub h2).add h3).congr_deriv (by ring)
          rw [hd.deriv]
          have : y⁻¹ - 1 + (y - 1) = (y - 1)^2 / y := by field_simp; ring
          rw [this]; positivity
      intro y hy
      have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
      simpa using this
    have := key x h1
    have h2 : (x - 1)^2 / 2 ≤ (x - 1)^2 / (2 * x₀) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    linarith
  · -- x < 1
    have key : ∀ y : ℝ, 0 < y → y ≤ 1 → 0 ≤ Real.log y - (y - y⁻¹) / 2 := by
      have hanti : AntitoneOn (fun y : ℝ => Real.log y - (y - y⁻¹) / 2) (Set.Ioc 0 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
        · apply ContinuousOn.sub
          · exact Real.continuousOn_log.mono (fun y hy => by simp at hy ⊢; linarith [hy.1])
          · apply ContinuousOn.div_const
            apply ContinuousOn.sub continuousOn_id
            exact continuousOn_inv₀.mono (fun y hy => by simp at hy ⊢; linarith [hy.1])
        · intro y hy
          have hy' : 0 < y := by simp at hy; linarith [hy.1]
          apply DifferentiableAt.differentiableWithinAt
          have := Real.differentiableAt_log hy'.ne'
          fun_prop (disch := exact hy'.ne')
        · intro y hy
          have hy' : 0 < y ∧ y < 1 := by simpa using hy
          have hy0 := hy'.1
          have hd : HasDerivAt (fun y : ℝ => Real.log y - (y - y⁻¹) / 2) (y⁻¹ - (1 + (y^2)⁻¹) / 2) y := by
            have h1 := Real.hasDerivAt_log hy0.ne'
            have h2 : HasDerivAt (fun y : ℝ => y⁻¹) (-(y^2)⁻¹) y := hasDerivAt_inv hy0.ne'
            have h3 := (((hasDerivAt_id y).sub h2).div_const 2)
            exact (h1.sub h3).congr_deriv (by simp)
          rw [hd.deriv]
          have : y⁻¹ - (1 + (y^2)⁻¹) / 2 = -((y - 1)^2 / (2 * y^2)) := by field_simp; ring
          rw [this]
          have : 0 ≤ (y - 1)^2 / (2 * y^2) := by positivity
          linarith
      intro y hy hy1
      have := hanti (Set.mem_Ioc.mpr ⟨hy, hy1⟩) (Set.mem_Ioc.mpr ⟨one_pos, le_rfl⟩) hy1
      simpa using this
    have := key x hx h1.le
    have h2 : (x - 1)^2 / (2 * x) ≤ (x - 1)^2 / (2 * x₀) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    have h3 : -(x - 1) + (x - 1)^2 / (2 * x) = -((x - x⁻¹) / 2) := by field_simp; ring
    linarith
