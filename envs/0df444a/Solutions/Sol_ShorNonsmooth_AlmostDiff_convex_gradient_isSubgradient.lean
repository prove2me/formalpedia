-- Prove2me | solution 1 for ShorNonsmooth.AlmostDiff.convex_gradient_isSubgradient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:46:41.958669+00:00
-- url     : https://prove2.me/submissions/cb4102b4-6aa6-4c24-877b-90b6ca7bdbe0

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient

open ShorNonsmooth.AlmostDiff in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (xk : EuclideanSpace ℝ (Fin n)) (hxk : DifferentiableAt ℝ f xk) :
    IsSubgradient f xk (gradient f xk) := by
  intro x
  set d := x - xk with hd
  -- line derivative
  have hline : HasDerivAt (fun t : ℝ => xk + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add xk
  have hφ : HasDerivAt (fun t : ℝ => f (xk + t • d)) (fderiv ℝ f xk d) 0 := by
    have hxk' : HasFDerivAt f (fderiv ℝ f xk) (xk + (0:ℝ) • d) := by
      simpa using hxk.hasFDerivAt
    exact hxk'.comp_hasDerivAt (x := (0:ℝ)) hline
  have hT := hφ.tendsto_slope_zero_right
  have hineq : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      t⁻¹ • (f (xk + (0 + t) • d) - f (xk + (0:ℝ) • d)) ≤ f x - f xk := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    have hc := hf.2 (Set.mem_univ xk) (Set.mem_univ x) (by linarith : (0:ℝ) ≤ 1 - t)
      ht0.le (by ring)
    have heq : (1 - t) • xk + t • x = xk + t • d := by
      rw [hd, smul_sub]; module
    rw [heq, smul_eq_mul, smul_eq_mul] at hc
    rw [inv_mul_le_iff₀ ht0]
    nlinarith
  have hle := le_of_tendsto hT hineq
  have hg : inner ℝ (gradient f xk) d = fderiv ℝ f xk d := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [ge_iff_le, hg]
  exact hle
