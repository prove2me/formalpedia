-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.idealVortex_scaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:53:05.368921+00:00
-- url     : https://prove2.me/submissions/5ab7b06a-c10e-45cc-bdd1-b41ab629fd1e

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

theorem g64h_lam (c W : ℝ) (z : V3) (i : Fin 3) (t : ℝ) :
    (![W / c ^ 2 * (z + t • (Pi.single i 1 : V3)) 0, W / c * (z + t • (Pi.single i 1 : V3)) 1,
      (z + t • (Pi.single i 1 : V3)) 2] : V3) =
    ![W / c ^ 2 * z 0, W / c * z 1, z 2] + (![W / c ^ 2, W / c, 1] i * t) • Pi.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [Pi.single_apply] <;> ring

theorem g64h_cp_scale (c W : ℝ) (S : V3 → ℝ) (z : V3) (i : Fin 3)
    (hS : DifferentiableAt ℝ S ![W / c ^ 2 * z 0, W / c * z 1, z 2]) :
    cartesianPartial (scaledEikonal c W S) z i =
      c / W * ![W / c ^ 2, W / c, 1] i * cartesianPartial S ![W / c ^ 2 * z 0, W / c * z 1, z 2] i := by
  set Az : V3 := ![W / c ^ 2 * z 0, W / c * z 1, z 2]
  have hA : DifferentiableAt ℝ (fun y : V3 => (![W / c ^ 2 * y 0, W / c * y 1, y 2] : V3)) z := by
    rw [differentiableAt_pi]
    intro j; fin_cases j <;> simp <;> fun_prop
  have hdt : DifferentiableAt ℝ (scaledEikonal c W S) z := by
    have := hS.comp z hA
    exact (this.const_mul (c / W))
  rw [g64h_cp _ _ _ hdt, g64h_cp _ _ _ hS]
  simp only [scaledEikonal, g64h_lam]
  have hline : HasDerivAt (fun t : ℝ => Az + t • Pi.single i (1:ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single i (1:ℝ))).const_add Az
  have hg : HasDerivAt (fun t : ℝ => S (Az + t • Pi.single i 1))
      (fderiv ℝ S Az (Pi.single i 1)) 0 := by
    have h0 : HasFDerivAt S (fderiv ℝ S Az) (Az + (0:ℝ) • Pi.single i 1) := by simpa using hS.hasFDerivAt
    exact h0.comp_hasDerivAt (0:ℝ) hline
  set lam := (![W / c ^ 2, W / c, 1] : V3) i
  have hm : HasDerivAt (fun t : ℝ => lam * t) lam 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_mul lam
  have hg' : HasDerivAt (fun t : ℝ => S (Az + t • Pi.single i 1)) (fderiv ℝ S Az (Pi.single i 1)) (lam * 0) := by
    simpa using hg
  have hc := (hg'.comp (0:ℝ) hm).const_mul (c / W)
  rw [hg.deriv]
  rw [show (fun t : ℝ => c / W * S (Az + (lam * t) • Pi.single i 1)) =
    (fun t => c / W * ((fun t : ℝ => S (Az + t • Pi.single i 1)) ∘ (fun t : ℝ => lam * t)) t) from rfl, hc.deriv]
  ring

/-- PDF pp.11–12, (100): coordinate pullback removes W from the ideal-vortex
Hamilton–Jacobi equation; phase is preserved by inverse frequency scaling.
This is not a fixed-distance W-to-zero or finite-core capture assertion. -/
theorem solution (c n W : ℝ) (S : V3 → ℝ) (z : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hW : 0 < W) (hz : 0 < z 1)
    (hS : DifferentiableAt ℝ S ![W / c ^ 2 * z 0, W / c * z 1, z 2]) :
    vortexSpeed c W (W / c * z 1) / c = vortexSpeed 1 1 (z 1) ∧
    cylindricalSymbol 1 n (vortexSpeed 1 1) (scaledEikonal c W S) z =
      cylindricalSymbol c n (vortexSpeed c W) S
        ![W / c ^ 2 * z 0, W / c * z 1, z 2] / c ^ 2 ∧
    (∀ (omega a r : ℝ), 0 < omega → 0 < a → 0 < r →
      vortexPhase c n (omega / a) (a * W) (a * r) = vortexPhase c n omega W r) ∧
    (∀ (a n0 : ℝ), 0 < a → 1 < n0 →
      criticalRadius c (a * W) n0 = a * criticalRadius c W n0) := by
  have hv : vortexSpeed c W (W / c * z 1) = c * vortexSpeed 1 1 (z 1) := by
    simp only [vortexSpeed, vortexGamma]
    have e : W ^ 2 / (c ^ 2 * (W / c * z 1) ^ 2) = 1 ^ 2 / (1 ^ 2 * z 1 ^ 2) := by
      field_simp
    rw [e]
    have : 0 < Real.sqrt (1 + 1 ^ 2 / (1 ^ 2 * z 1 ^ 2)) := Real.sqrt_pos.2 (by positivity)
    field_simp
  have hint : ∀ W' r' φ : ℝ, r' ≠ 0 → dot3 (slowVortexPolar W' r' φ) (r' • azimuth φ) = W' := by
    intro W' r' φ hr
    simp only [dot3, slowVortexPolar, azimuth, Fin.sum_univ_three]
    simp
    field_simp
    linear_combination W' * Real.sin_sq_add_cos_sq φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hv]; field_simp
  · simp only [cylindricalSymbol]
    rw [g64h_cp_scale c W S z 0 hS, g64h_cp_scale c W S z 1 hS, g64h_cp_scale c W S z 2 hS]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [hv]
    have hz0 : z 1 ≠ 0 := hz.ne'
    have hW0 : W ≠ 0 := hW.ne'
    have hc0 : c ≠ 0 := hc.ne'
    have h1 : 1 - vortexSpeed 1 1 (z 1) ^ 2 / 1 ^ 2 ≠ 0 := by
      have hg2 : vortexGamma 1 1 (z 1) ^ 2 = 1 + 1 ^ 2 / (1 ^ 2 * z 1 ^ 2) := by
        rw [vortexGamma, Real.sq_sqrt (by positivity)]
      have hgp : 0 < vortexGamma 1 1 (z 1) := Real.sqrt_pos.2 (by positivity)
      have hgs : 1 < vortexGamma 1 1 (z 1) * z 1 := by
        have : (vortexGamma 1 1 (z 1) * z 1) ^ 2 = z 1 ^ 2 + 1 := by
          rw [mul_pow, hg2]; field_simp
        nlinarith [mul_pos hgp hz]
      have hv1 : vortexSpeed 1 1 (z 1) < 1 := by
        rw [vortexSpeed, div_lt_one (by positivity)]; exact hgs
      have hv0 : 0 < vortexSpeed 1 1 (z 1) := by rw [vortexSpeed]; positivity
      have : vortexSpeed 1 1 (z 1) ^ 2 < 1 := by nlinarith
      intro h; simp at h; linarith
    have h2 : 1 - (c * vortexSpeed 1 1 (z 1)) ^ 2 / c ^ 2 ≠ 0 := by
      have : (c * vortexSpeed 1 1 (z 1)) ^ 2 / c ^ 2 = vortexSpeed 1 1 (z 1) ^ 2 / 1 ^ 2 := by
        field_simp
      rw [this]; exact h1
    field_simp
  · intro omega a r ho ha hr
    simp only [vortexPhase, hint _ _ _ hr.ne', hint _ _ _ (mul_pos ha hr).ne',
      intervalIntegral.integral_const, smul_eq_mul]
    field_simp
  · intro a n0 ha hn0
    simp only [criticalRadius]
    ring


end

