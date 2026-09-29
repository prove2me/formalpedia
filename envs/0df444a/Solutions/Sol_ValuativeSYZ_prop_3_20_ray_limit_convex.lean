-- Prove2me | solution 1 for ValuativeSYZ.prop_3_20_ray_limit_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:53:15.977351+00:00
-- url     : https://prove2.me/submissions/7d957368-af63-4f4f-b943-c4631c63c22f

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

/-! 76b185d6 ValuativeSYZ.prop_3_20_ray_limit_convex (convexity of the ray limits).

Route. Multiply each normalised sequence by its ray length: `l * (F (m*l) (m•q) / (m*l))`
equals `F (m*l) (m•q) / m` for `m > 0`, so these converge to `l*g`, `l'*g'`, `(l+l')*h`.
Subadditivity with `m*(l+l') = m*l + m*l'` and `m•(q+q') = m•q + m•q'` gives the pointwise
inequality after dividing by `m`, and `le_of_tendsto_of_tendsto` passes it to the limits. -/

set_option autoImplicit false

open MeasureTheory

open ValuativeSYZ in
theorem solution {n : ℕ} (F : ℕ → (Fin n → ℤ) → ℝ)
    (hsub : ∀ (l l' : ℕ) (q q' : Fin n → ℤ), F (l + l') (q + q') ≤ F l q + F l' q')
    (l l' : ℕ) (hl : 0 < l) (hl' : 0 < l') (q q' : Fin n → ℤ) (g g' h : ℝ)
    (hg : Filter.Tendsto (fun m : ℕ => F (m * l) (m • q) / (m * l)) Filter.atTop (nhds g))
    (hg' : Filter.Tendsto (fun m : ℕ => F (m * l') (m • q') / (m * l')) Filter.atTop (nhds g'))
    (hh : Filter.Tendsto (fun m : ℕ => F (m * (l + l')) (m • (q + q')) / (m * (l + l')))
      Filter.atTop (nhds h)) :
    ((l : ℝ) + l') * h ≤ l * g + l' * g' := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hlR' : (0 : ℝ) < l' := by exact_mod_cast hl'
  have h1 := (hg.const_mul (l : ℝ)).add (hg'.const_mul (l' : ℝ))
  have h2 := hh.const_mul ((l : ℝ) + l')
  refine le_of_tendsto_of_tendsto h2 h1 ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have key := hsub (m * l) (m * l') (m • q) (m • q')
  rw [← mul_add, ← smul_add] at key
  have e1 : ((l : ℝ) + l') * (F (m * (l + l')) (m • (q + q')) / (m * (l + l')))
      = F (m * (l + l')) (m • (q + q')) / m := by
    field_simp
  have e2 : (l : ℝ) * (F (m * l) (m • q) / (m * l)) = F (m * l) (m • q) / m := by
    field_simp
  have e3 : (l' : ℝ) * (F (m * l') (m • q') / (m * l')) = F (m * l') (m • q') / m := by
    field_simp
  rw [e1, e2, e3, ← add_div]
  exact div_le_div_of_nonneg_right key hmR.le
