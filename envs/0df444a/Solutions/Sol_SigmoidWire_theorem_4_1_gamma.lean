-- Prove2me | solution 1 for SigmoidWire.theorem_4_1_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-13T02:09:58.537791+00:00
-- url     : https://prove2.me/submissions/455065e2-7233-4b56-82bb-cb95f686d0e1

import Mathlib

theorem solution :
    (∀ ξ ∈ Set.Icc (0 : ℝ) 1, (1 / 6 : ℝ) ≤ deriv Real.sigmoid ξ) ∧
    deriv Real.sigmoid 1 = Real.exp 1 / (1 + Real.exp 1) ^ 2 ∧
    (1 / 6 : ℝ) < Real.exp 1 / (1 + Real.exp 1) ^ 2 ∧
    StrictAntiOn (deriv Real.sigmoid) (Set.Ici 0) ∧
    ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
      (1 / 6 : ℝ) * (v - u) ≤ Real.sigmoid v - Real.sigmoid u := by
  have hd : ∀ x, deriv Real.sigmoid x = Real.sigmoid x * (1 - Real.sigmoid x) := fun x => by
    rw [Real.deriv_sigmoid]
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he2 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hval : deriv Real.sigmoid 1 = Real.exp 1 / (1 + Real.exp 1) ^ 2 := by
    rw [hd, Real.sigmoid_def, Real.exp_neg]
    have : 0 < Real.exp 1 := Real.exp_pos 1
    field_simp
    ring
  have hgt : (1 / 6 : ℝ) < Real.exp 1 / (1 + Real.exp 1) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hhalf : ∀ x : ℝ, 0 ≤ x → 1 / 2 ≤ Real.sigmoid x := fun x hx => by
    have := Real.sigmoid_le hx
    rw [Real.sigmoid_zero] at this
    linarith
  have hanti : StrictAntiOn (deriv Real.sigmoid) (Set.Ici 0) := by
    intro x hx y hy hxy
    rw [hd, hd]
    have h1 := hhalf x hx
    have h2 := Real.sigmoid_lt hxy
    nlinarith
  have hbound : ∀ ξ ∈ Set.Icc (0 : ℝ) 1, (1 / 6 : ℝ) ≤ deriv Real.sigmoid ξ := by
    intro ξ hξ
    rcases eq_or_lt_of_le hξ.2 with h | h
    · rw [h, hval]; exact hgt.le
    · have := hanti (Set.mem_Ici.mpr hξ.1) (Set.mem_Ici.mpr zero_le_one) h
      rw [hval] at this
      linarith
  refine ⟨hbound, hval, hgt, hanti, ?_⟩
  intro u v hu huv hv
  exact (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv continuous_sigmoid.continuousOn
    differentiable_sigmoid.differentiableOn (fun x hx => hbound x (interior_subset hx))
    u ⟨hu, huv.trans hv⟩ v ⟨hu.trans huv, hv⟩ huv
