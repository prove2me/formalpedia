-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.opticalAharonovBohm_phase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:24:50.074054+00:00
-- url     : https://prove2.me/submissions/c8f47fd5-5457-48bf-8da7-99ff14f7700f

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem g64h_cp {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    (hf : DifferentiableAt ℝ f x) :
    cartesianPartial f x i = deriv (fun t : ℝ => f (x + t • Pi.single i 1)) 0 := by
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => WithLp.ofLp y)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ) : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))
      (WithLp.toLp 2 x) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.hasFDerivAt
  have hf' : HasFDerivAt f (fderiv ℝ f x) (WithLp.ofLp (WithLp.toLp 2 x)) := hf.hasFDerivAt
  have hc := hf'.comp (WithLp.toLp 2 x) hL
  have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single i (1:ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single i (1:ℝ))).const_add x
  have h2 := (by simpa using hf.hasFDerivAt : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • Pi.single i 1)).comp_hasDerivAt (0:ℝ) hline
  rw [show (fun t : ℝ => f (x + t • Pi.single i 1)) = (f ∘ fun t => x + t • Pi.single i 1) from rfl,
    h2.deriv, cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial]
  simp only
  rw [show (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y)) = f ∘ WithLp.ofLp from rfl, hc.fderiv]
  simp [EuclideanSpace.single]
  congr 1

theorem g64h_dq (W a b : ℝ) (h : 0 < a ^ 2 + b ^ 2) :
    HasDerivAt (fun t : ℝ => W / ((a + t) ^ 2 + b ^ 2) * (a + t))
      (W * (b ^ 2 - a ^ 2) / (a ^ 2 + b ^ 2) ^ 2) 0 := by
  have hl : HasDerivAt (fun t : ℝ => a + t) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add a
  have hden : HasDerivAt (fun t : ℝ => (a + t) ^ 2 + b ^ 2) (2 * (a + 0) * 1) 0 := by
    simpa using (hl.pow 2).add_const (b ^ 2)
  have hne : (a + 0) ^ 2 + b ^ 2 ≠ 0 := by simpa using h.ne'
  have := ((hasDerivAt_const (0:ℝ) W).fun_div hden hne).fun_mul hl
  refine this.congr_deriv ?_
  have h0 : a ^ 2 + b ^ 2 ≠ 0 := h.ne'
  simp only [add_zero, mul_one, zero_mul, zero_sub]
  field_simp
  ring

theorem g64h_dq' (W a b : ℝ) (h : 0 < a ^ 2 + b ^ 2) :
    HasDerivAt (fun t : ℝ => W / (b ^ 2 + (a + t) ^ 2) * (a + t))
      (W * (b ^ 2 - a ^ 2) / (a ^ 2 + b ^ 2) ^ 2) 0 := by
  have := g64h_dq W a b h
  convert this using 2 with t
  ring

theorem g64h_curl (W : ℝ) (x : V3) (hx : 0 < x 0 ^ 2 + x 1 ^ 2) :
      curl3 (fun y => (W / (y 0 ^ 2 + y 1 ^ 2)) • ![-y 1, y 0, 0]) x = 0 := by
  have hq : DifferentiableAt ℝ (fun y : V3 => W / (y 0 ^ 2 + y 1 ^ 2)) x :=
    by fun_prop (disch := exact hx.ne')
  have h0 : DifferentiableAt ℝ (fun y : V3 => -(W / (y 0 ^ 2 + y 1 ^ 2) * y 1)) x :=
    (hq.mul (by fun_prop)).neg
  have h1 : DifferentiableAt ℝ (fun y : V3 => W / (y 0 ^ 2 + y 1 ^ 2) * y 0) x :=
    (hq.mul (by fun_prop))
  have hz : ∀ i, cartesianPartial (fun _ : V3 => (0:ℝ)) x i = 0 := by
    intro i; rw [g64h_cp _ _ _ (differentiableAt_const _)]; simp
  ext k
  fin_cases k <;> simp only [curl3] <;> simp [hz]
  · rw [g64h_cp _ _ _ h1]; simp
  · rw [g64h_cp _ _ _ h0]; simp
  · rw [g64h_cp _ _ _ h0, g64h_cp _ _ _ h1]; simp
    rw [(g64h_dq W (x 0) (x 1) hx).deriv, (g64h_dq' W (x 1) (x 0) (by linarith)).deriv]
    ring

/-- PDF p.7, (62)–(64): one positive circuit in the stipulated first-order
magnetic optical model gives the optical Aharonov–Bohm phase. -/
theorem solution (c n omega W r : ℝ)
    (hc : 0 < c) (hn : 1 ≤ n) (ho : 0 < omega) (hW : 0 < W) (hr : 0 < r) :
    vortexPhase c n omega W r = 2 * Real.pi * (omega / c) * (n ^ 2 - 1) * (W / c) ∧
    (∀ x : V3, 0 < x 0 ^ 2 + x 1 ^ 2 →
      curl3 (fun y => (W / (y 0 ^ 2 + y 1 ^ 2)) • ![-y 1, y 0, 0]) x = 0) ∧
    (∀ turns : ℕ,
      ((n ^ 2 - 1) * omega / c ^ 2) *
        (∫ phi in (0 : ℝ)..((turns : ℝ) * (2 * Real.pi)),
          dot3 (slowVortexPolar W r phi) (r • azimuth phi)) =
        (turns : ℝ) * vortexPhase c n omega W r) := by
  have hint : ∀ φ, dot3 (slowVortexPolar W r φ) (r • azimuth φ) = W := by
    intro φ
    simp only [dot3, slowVortexPolar, azimuth, Fin.sum_univ_three]
    simp
    field_simp
    linear_combination Real.sin_sq_add_cos_sq φ
  have hph : vortexPhase c n omega W r = ((n ^ 2 - 1) * omega / c ^ 2) * (2 * Real.pi * W) := by
    simp only [vortexPhase, hint, intervalIntegral.integral_const, smul_eq_mul]; ring
  refine ⟨?_, fun x hx => g64h_curl W x hx, fun turns => ?_⟩
  · rw [hph]; field_simp
  · simp only [hint, intervalIntegral.integral_const, smul_eq_mul]
    rw [hph]; ring


end

