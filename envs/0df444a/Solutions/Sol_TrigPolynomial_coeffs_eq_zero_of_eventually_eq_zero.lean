-- Prove2me | solution 1 for TrigPolynomial.coeffs_eq_zero_of_eventually_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T00:01:19.94939+00:00
-- url     : https://prove2.me/submissions/a5e3ac38-6cf4-4977-9a2b-cb7f75135e9e

import Mathlib

open Filter Topology

theorem solution (k : ℝ) (hk : k ≠ 0) (D A B x0 : ℝ)
    (h : ∀ᶠ x in 𝓝 x0, D + A * Real.cos (k * x) + B * Real.sin (k * x) = 0) :
    D = 0 ∧ A = 0 ∧ B = 0 := by
  set f : ℝ → ℝ := fun x => D + A * Real.cos (k * x) + B * Real.sin (k * x) with hf
  have hfd : ∀ x : ℝ, HasDerivAt f
      (-(A * k) * Real.sin (k * x) + (B * k) * Real.cos (k * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => k * x) k x := by
      simpa using (hasDerivAt_id x).const_mul k
    have hc : HasDerivAt (fun x : ℝ => Real.cos (k * x)) (-Real.sin (k * x) * k) x :=
      (Real.hasDerivAt_cos (k * x)).comp x h1
    have hs : HasDerivAt (fun x : ℝ => Real.sin (k * x)) (Real.cos (k * x) * k) x :=
      (Real.hasDerivAt_sin (k * x)).comp x h1
    have := ((hasDerivAt_const x D).fun_add (hc.const_mul A)).fun_add (hs.const_mul B)
    exact this.congr_deriv (by ring)
  set g : ℝ → ℝ := fun x => -(A * k) * Real.sin (k * x) + (B * k) * Real.cos (k * x) with hg
  have hgd : ∀ x : ℝ, HasDerivAt g
      (-(A * k * k) * Real.cos (k * x) - (B * k * k) * Real.sin (k * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => k * x) k x := by
      simpa using (hasDerivAt_id x).const_mul k
    have hc : HasDerivAt (fun x : ℝ => Real.cos (k * x)) (-Real.sin (k * x) * k) x :=
      (Real.hasDerivAt_cos (k * x)).comp x h1
    have hs : HasDerivAt (fun x : ℝ => Real.sin (k * x)) (Real.cos (k * x) * k) x :=
      (Real.hasDerivAt_sin (k * x)).comp x h1
    have := (hs.const_mul (-(A * k))).fun_add (hc.const_mul (B * k))
    exact this.congr_deriv (by ring)
  -- f vanishes near x0, hence so do g and its derivative
  have hg0 : ∀ᶠ x in 𝓝 x0, g x = 0 := by
    have hopen : ∀ᶠ x in 𝓝 x0, ∀ᶠ y in 𝓝 x, f y = 0 := by
      obtain ⟨s, hsub, hso, hx0⟩ := mem_nhds_iff.mp h
      filter_upwards [hso.mem_nhds hx0] with x hx
      filter_upwards [hso.mem_nhds hx] with y hy
      exact hsub hy
    filter_upwards [hopen] with x hx
    have hev : f =ᶠ[𝓝 x] fun _ : ℝ => (0:ℝ) := by filter_upwards [hx] with y hy using hy
    exact (hev.hasDerivAt_iff.mp (hfd x)).unique (hasDerivAt_const x 0)
  have hgder0 :
      -(A * k * k) * Real.cos (k * x0) - (B * k * k) * Real.sin (k * x0) = 0 := by
    have hev : g =ᶠ[𝓝 x0] fun _ : ℝ => (0:ℝ) := by filter_upwards [hg0] with y hy using hy
    exact (hev.hasDerivAt_iff.mp (hgd x0)).unique (hasDerivAt_const x0 0)
  have hgx0 : -(A * k) * Real.sin (k * x0) + (B * k) * Real.cos (k * x0) = 0 :=
    hg0.self_of_nhds
  have hfx0 : D + A * Real.cos (k * x0) + B * Real.sin (k * x0) = 0 := h.self_of_nhds
  have hpyth := Real.sin_sq_add_cos_sq (k * x0)
  have hkk : k * k ≠ 0 := mul_ne_zero hk hk
  have e1 : A * Real.cos (k * x0) + B * Real.sin (k * x0) = 0 := by
    have hz : (k * k) * (A * Real.cos (k * x0) + B * Real.sin (k * x0)) = 0 := by
      linear_combination -hgder0
    rcases mul_eq_zero.mp hz with hcon | hres
    · exact absurd hcon hkk
    · exact hres
  have e2 : -(A * Real.sin (k * x0)) + B * Real.cos (k * x0) = 0 := by
    have hz : k * (-(A * Real.sin (k * x0)) + B * Real.cos (k * x0)) = 0 := by
      linear_combination hgx0
    rcases mul_eq_zero.mp hz with hcon | hres
    · exact absurd hcon hk
    · exact hres
  have hA : A = 0 := by
    linear_combination Real.cos (k * x0) * e1 - Real.sin (k * x0) * e2 - A * hpyth
  have hB : B = 0 := by
    linear_combination Real.sin (k * x0) * e1 + Real.cos (k * x0) * e2 - B * hpyth
  refine ⟨?_, hA, hB⟩
  rw [hA, hB] at hfx0; linarith
