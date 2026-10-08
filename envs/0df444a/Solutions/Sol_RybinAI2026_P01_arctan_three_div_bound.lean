-- Prove2me | solution 1 for RybinAI2026.P01.arctan_three_div_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T07:12:46.000373+00:00
-- url     : https://prove2.me/submissions/28010943-b5e9-406a-96ba-5c54cc156522

-- Candidate v2 for arctan_three_div_bound (repair-of 7148: explicit arg + RAW (0+2x) everywhere, exact-div) — remote verification authoritative.
-- Step-3 core for future RybinAI2026.P01.h_sq_strict_concave candidate:
-- arctan u > 3u/(3+u^2) for u > 0, via StrictMonoOn from positive derivative.
-- Names verified present in pinned rev c5ea003 on 2026-10-05:
-- Real.hasDerivAt_arctan, strictMonoOn_of_deriv_pos, HasDerivAt combinators.
-- Remote verification still required after integration into the full proof.

import Mathlib
set_option autoImplicit false

-- The comparison function and its derivative identity:
-- d/du [arctan u - 3u/(3+u^2)] = 4u^4/((1+u^2)(3+u^2)^2).
-- Check: 1/(1+u^2) - (9-3u^2)/(3+u^2)^2
--   = [(3+u^2)^2 - (9-3u^2)(1+u^2)]/((1+u^2)(3+u^2)^2)
--   = [9+6u^2+u^4-9-6u^2+3u^4]/den = 4u^4/den. Verified by hand.
theorem solution (u : ℝ) (hu : 0 < u) :
    3 * u / (3 + u ^ 2) < Real.arctan u := by
  set f : ℝ → ℝ := fun u => Real.arctan u - 3 * u / (3 + u ^ 2) with hf
  have hcont : ContinuousOn f (Set.Ici 0) := by
    apply ContinuousOn.sub Real.continuous_arctan.continuousOn
    apply ContinuousOn.div
    · exact (continuous_const.mul continuous_id).continuousOn
    · exact (continuous_const.add (continuous_id.pow 2)).continuousOn
    · intro x _
      exact ne_of_gt (by positivity : (0 : ℝ) < 3 + x ^ 2)
  have hderiv : ∀ x : ℝ, x ∈ interior (Set.Ici (0 : ℝ)) →
      0 < deriv f x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by
      have := interior_Ici (a := (0 : ℝ))
      simpa [this] using hx
    have ha : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
      Real.hasDerivAt_arctan x
    have hb : HasDerivAt (fun u : ℝ => 3 * u / (3 + u ^ 2))
        ((3 * (3 + x ^ 2) - 3 * x * (0 + 2 * x)) / (3 + x ^ 2) ^ 2) x := by
      have hnum : HasDerivAt (fun u : ℝ => 3 * u) 3 x := hasDerivAt_const_mul 3
      have hdnm : HasDerivAt (fun u : ℝ => 3 + u ^ 2) (0 + 2 * x) x := by
        have ha3 : HasDerivAt (fun _ : ℝ => (3 : ℝ)) 0 x := hasDerivAt_const x 3
        have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
          have h := hasDerivAt_pow 2 x
          simpa using h
        exact ha3.add h2
      exact hnum.div hdnm (ne_of_gt (by positivity : (0 : ℝ) < 3 + x ^ 2))
    have hfab : HasDerivAt f (1 / (1 + x ^ 2)
        - (3 * (3 + x ^ 2) - 3 * x * (0 + 2 * x)) / (3 + x ^ 2) ^ 2) x :=
      ha.sub hb
    have hval : 1 / (1 + x ^ 2)
        - (3 * (3 + x ^ 2) - 3 * x * (0 + 2 * x)) / (3 + x ^ 2) ^ 2
        = 4 * x ^ 4 / ((1 + x ^ 2) * (3 + x ^ 2) ^ 2) := by
      have h1 : (1 : ℝ) + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have h3 : (3 : ℝ) + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring
    rw [hfab.deriv, hval]
    apply div_pos _ _ 
    · exact mul_pos (by norm_num) (pow_pos hx0 4)
    · exact mul_pos (by positivity) (pow_pos (by positivity) 2)
  have hmono : StrictMonoOn f (Set.Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont hderiv
  have h0 : f 0 = 0 := by simp [hf, Real.arctan_zero]
  have hlt := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu.le) hu
  rw [h0] at hlt
  have : f u = Real.arctan u - 3 * u / (3 + u ^ 2) := rfl
  linarith
