-- Prove2me | solution 1 for ProjReflGrad.Linear.solSet_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:20:50.068607+00:00
-- url     : https://prove2.me/submissions/5998d31b-d5e3-4809-b231-7e5ecd6a96da

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

set_option autoImplicit false

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (m : ℝ) (hm : 0 < m) (hC2s : ProjReflGrad.Linear.IsStronglyMonotoneMap F m) :
    (ProjReflGrad.Weak.solSet C F).Subsingleton := by
  intro a ha b hb
  have h1 := ha.2 b hb.1
  have h2 := hb.2 a ha.1
  have h3 := hC2s a b
  have h4 : inner ℝ (F a - F b) (a - b) = -(inner ℝ (F a) (b - a)) - inner ℝ (F b) (a - b) := by
    simp only [inner_sub_left, inner_sub_right]; ring
  have h5 : m * ‖a - b‖ ^ 2 ≤ 0 := by linarith
  have h6 : ‖a - b‖ ^ 2 ≤ 0 := by
    by_contra hc; push Not at hc; nlinarith
  have h7 : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h7)
