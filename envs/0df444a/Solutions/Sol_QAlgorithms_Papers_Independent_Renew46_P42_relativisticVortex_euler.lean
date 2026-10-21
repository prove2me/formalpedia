-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.relativisticVortex_euler
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:34:37.281984+00:00
-- url     : https://prove2.me/submissions/d2a87fe6-d3cf-4825-addd-5f1b3f427a49

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem g65c_cp {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
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

theorem g65c_cp_const {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    (h : ∀ t : ℝ, f (x + t • Pi.single i 1) = f x) : cartesianPartial f x i = 0 := by
  by_cases hd : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y)) (WithLp.toLp 2 x)
  · have hf : DifferentiableAt ℝ f x := by
      have h2 : DifferentiableAt ℝ (fun z : Fin d → ℝ => WithLp.toLp 2 z) x :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.differentiableAt
      have := hd.comp x h2
      simpa [Function.comp_def] using this
    rw [g65c_cp f x i hf]
    simp [h]
  · simp [cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial,
      fderiv_zero_of_not_differentiableAt hd]

theorem g65c_K_line (K : ℝ → ℝ) (K' a b : ℝ) (hK : HasDerivAt K K' (a ^ 2 + b ^ 2)) :
    HasDerivAt (fun t : ℝ => K ((a + t) ^ 2 + b ^ 2)) (K' * (2 * a)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => a + t) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add a
  have hin : HasDerivAt (fun t : ℝ => (a + t) ^ 2 + b ^ 2) (2 * a) 0 := by
    simpa using ((hl.pow 2).add_const (b ^ 2))
  have hK' : HasDerivAt K K' ((a + 0) ^ 2 + b ^ 2) := by simpa using hK
  exact hK'.comp 0 hin

theorem g65c_K_line2 (K : ℝ → ℝ) (K' a b : ℝ) (hK : HasDerivAt K K' (a ^ 2 + b ^ 2)) :
    HasDerivAt (fun t : ℝ => K (a ^ 2 + (b + t) ^ 2)) (K' * (2 * b)) 0 := by
  have := g65c_K_line K K' b a (by rw [add_comm]; exact hK)
  simpa [add_comm] using this

theorem g65c_euler (c W rho : ℝ) (x : V4)
    (hc : 0 < c) (hx : 0 < axisRadius x) :
    (∀ j : Fin 4, (∑ i, cartesianPartial (fun y => vortexStress c W rho y i j) x i) = 0) := by
  have hR : ∀ y : V4, axisRadius y ^ 2 = y 1 ^ 2 + y 2 ^ 2 := fun y => by
    rw [axisRadius, Real.sq_sqrt (by positivity)]
  have hρ : 0 < x 1 ^ 2 + x 2 ^ 2 := by rw [← hR]; positivity
  set ρ := x 1 ^ 2 + x 2 ^ 2 with hρdef
  set P : ℝ → ℝ := fun s => rho * c ^ 2 * Real.exp (-W ^ 2 / (2 * c ^ 2 * s)) - rho * c ^ 2 with hP
  set G : ℝ → ℝ := fun s => (rho * c ^ 2 + P s) * W ^ 2 / (c ^ 2 * s ^ 2) with hG
  set K : ℝ → ℝ := fun s => (rho * c ^ 2 + P s) * (W / (c * s)) * Real.sqrt (1 + W ^ 2 / (c ^ 2 * s)) with hK
  have hpr : ∀ y : V4, vortexPressure c W rho (axisRadius y) = P (y 1 ^ 2 + y 2 ^ 2) := by
    intro y; simp only [vortexPressure, hP, hR]
  have hgam : ∀ y : V4, vortexGamma c W (axisRadius y) = Real.sqrt (1 + W ^ 2 / (c ^ 2 * (y 1 ^ 2 + y 2 ^ 2))) := by
    intro y; simp only [vortexGamma, mul_pow, hR]
  -- derivatives
  have hc2 : 0 < c ^ 2 := by positivity
  have hdP : HasDerivAt P (rho * c ^ 2 * Real.exp (-W ^ 2 / (2 * c ^ 2 * ρ)) * (W ^ 2 / (2 * c ^ 2 * ρ ^ 2))) ρ := by
    have h1 : HasDerivAt (fun s : ℝ => -W ^ 2 / (2 * c ^ 2 * s)) (W ^ 2 / (2 * c ^ 2 * ρ ^ 2)) ρ := by
      have hne : 2 * c ^ 2 * ρ ≠ 0 := by positivity
      have := (hasDerivAt_const ρ (-W ^ 2)).fun_div ((hasDerivAt_id' ρ).const_mul (2 * c ^ 2)) hne
      refine this.congr_deriv ?_
      field_simp; ring
    have := ((h1.exp).const_mul (rho * c ^ 2)).sub_const (rho * c ^ 2)
    exact this.congr_deriv (by ring)
  have hdPd : DifferentiableAt ℝ P ρ := hdP.differentiableAt
  have hdG : DifferentiableAt ℝ G ρ := by
    have : c ^ 2 * ρ ^ 2 ≠ 0 := by positivity
    exact (((differentiableAt_const _).add hdPd).mul (differentiableAt_const _)).div (by fun_prop) this
  have hdK : DifferentiableAt ℝ K ρ := by
    have h0 : c * ρ ≠ 0 := by positivity
    have h1 : 0 < 1 + W ^ 2 / (c ^ 2 * ρ) := by positivity
    have h2 : DifferentiableAt ℝ (fun s : ℝ => 1 + W ^ 2 / (c ^ 2 * s)) ρ := by
      have : c ^ 2 * ρ ≠ 0 := by positivity
      fun_prop (disch := exact this)
    exact (((differentiableAt_const _).add hdPd).mul ((differentiableAt_const _).div (by fun_prop) h0)).mul
      (h2.sqrt h1.ne')
  have hGd := hdG.hasDerivAt
  have hKd := hdK.hasDerivAt
  have hKρ : ∀ (F : ℝ → ℝ), DifferentiableAt ℝ F ρ → DifferentiableAt ℝ (fun y : V4 => F (y 1 ^ 2 + y 2 ^ 2)) x :=
    fun F hF => hF.comp (f := fun y : V4 => y 1 ^ 2 + y 2 ^ 2) x (by fun_prop)
  intro j
  simp only [Fin.sum_univ_four]
  fin_cases j
  · -- j = 0
    have e1 : (fun y => vortexStress c W rho y 1 0) = fun y => K (y 1 ^ 2 + y 2 ^ 2) * (-y 2) := by
      funext y
      simp only [vortexStress, vortexFour, minkowskiMetric, hpr, hgam, hK, hR]
      simp
      ring
    have e2 : (fun y => vortexStress c W rho y 2 0) = fun y => K (y 1 ^ 2 + y 2 ^ 2) * (y 1) := by
      funext y
      simp only [vortexStress, vortexFour, minkowskiMetric, hpr, hgam, hK, hR]
      simp
      ring
    simp only [Fin.zero_eta, Fin.isValue]
    have d1 : DifferentiableAt ℝ (fun y : V4 => K (y 1 ^ 2 + y 2 ^ 2) * -y 2) x := (hKρ K hdK).mul (by fun_prop)
    have d2 : DifferentiableAt ℝ (fun y : V4 => K (y 1 ^ 2 + y 2 ^ 2) * y 1) x := (hKρ K hdK).mul (by fun_prop)
    rw [g65c_cp_const _ _ 0 (fun t => by simp [vortexStress, vortexFour, vortexGamma, vortexPressure, axisRadius]),
      g65c_cp_const _ _ 3 (fun t => by simp [vortexStress, vortexFour, minkowskiMetric]), e1, e2,
      g65c_cp _ _ _ d1, g65c_cp _ _ _ d2]
    simp
    rw [(g65c_K_line K _ (x 1) (x 2) hKd).deriv,
      (g65c_K_line2 K _ (x 1) (x 2) hKd).deriv]
    ring

  · -- j = 1
    have e1 : (fun y => vortexStress c W rho y 1 1) = fun y => G (y 1 ^ 2 + y 2 ^ 2) * y 2 ^ 2 + P (y 1 ^ 2 + y 2 ^ 2) := by
      funext y
      simp only [vortexStress, vortexFour, minkowskiMetric, hpr, hG, hR]
      generalize y 1 ^ 2 + y 2 ^ 2 = s
      simp
      ring
    have e2 : (fun y => vortexStress c W rho y 2 1) = fun y => -(G (y 1 ^ 2 + y 2 ^ 2) * (y 1 * y 2)) := by
      funext y
      simp only [vortexStress, vortexFour, minkowskiMetric, hpr, hG, hR]
      generalize y 1 ^ 2 + y 2 ^ 2 = s
      simp
      ring
    have d1 : DifferentiableAt ℝ (fun y : V4 => G (y 1 ^ 2 + y 2 ^ 2) * y 2 ^ 2 + P (y 1 ^ 2 + y 2 ^ 2)) x :=
      ((hKρ G hdG).mul (by fun_prop)).add (hKρ P hdPd)
    have d2 : DifferentiableAt ℝ (fun y : V4 => -(G (y 1 ^ 2 + y 2 ^ 2) * (y 1 * y 2))) x :=
      ((hKρ G hdG).mul (by fun_prop)).neg
    have C1 : cartesianPartial (fun y : V4 => G (y 1 ^ 2 + y 2 ^ 2) * y 2 ^ 2 + P (y 1 ^ 2 + y 2 ^ 2)) x 1 =
        deriv G ρ * (2 * x 1) * x 2 ^ 2 + deriv P ρ * (2 * x 1) := by
      rw [g65c_cp _ _ _ d1]; apply HasDerivAt.deriv
      have H := ((g65c_K_line G _ (x 1) (x 2) hGd).mul_const (x 2 ^ 2)).add
        (g65c_K_line P _ (x 1) (x 2) hdPd.hasDerivAt)
      convert H using 1
      funext t; simp
    have C2 : cartesianPartial (fun y : V4 => -(G (y 1 ^ 2 + y 2 ^ 2) * (y 1 * y 2))) x 2 =
        -(deriv G ρ * (2 * x 2) * (x 1 * x 2) + G ρ * x 1) := by
      rw [g65c_cp _ _ _ d2]; apply HasDerivAt.deriv
      have hl : HasDerivAt (fun t : ℝ => x 1 * (x 2 + t)) (x 1) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).const_add (x 2)).const_mul (x 1)
      have H := ((g65c_K_line2 G _ (x 1) (x 2) hGd).mul hl).neg
      convert H using 1
      · funext t; simp
      · simp [hρdef]
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [g65c_cp_const _ _ 0 (fun t => by simp [vortexStress, vortexFour, vortexGamma, vortexPressure, axisRadius]),
      g65c_cp_const _ _ 3 (fun t => by simp [vortexStress, vortexFour, minkowskiMetric]), e1, e2, C1, C2,
      hdP.deriv]
    simp only [hG, hP]
    field_simp
    ring
  · -- j = 2
    have e1 : (fun y => vortexStress c W rho y 2 2) = fun y => G (y 1 ^ 2 + y 2 ^ 2) * y 1 ^ 2 + P (y 1 ^ 2 + y 2 ^ 2) := by
      funext y
      simp only [vortexStress, vortexFour, minkowskiMetric, hpr, hG, hR]
      generalize y 1 ^ 2 + y 2 ^ 2 = s
      simp
      ring
    have e2 : (fun y => vortexStress c W rho y 1 2) = fun y => -(G (y 1 ^ 2 + y 2 ^ 2) * (y 1 * y 2)) := by
      funext y
      simp only [vortexStress, vortexFour, minkowskiMetric, hpr, hG, hR]
      generalize y 1 ^ 2 + y 2 ^ 2 = s
      simp
      ring
    have d1 : DifferentiableAt ℝ (fun y : V4 => G (y 1 ^ 2 + y 2 ^ 2) * y 1 ^ 2 + P (y 1 ^ 2 + y 2 ^ 2)) x :=
      ((hKρ G hdG).mul (by fun_prop)).add (hKρ P hdPd)
    have d2 : DifferentiableAt ℝ (fun y : V4 => -(G (y 1 ^ 2 + y 2 ^ 2) * (y 1 * y 2))) x :=
      ((hKρ G hdG).mul (by fun_prop)).neg
    have C1 : cartesianPartial (fun y : V4 => G (y 1 ^ 2 + y 2 ^ 2) * y 1 ^ 2 + P (y 1 ^ 2 + y 2 ^ 2)) x 2 =
        deriv G ρ * (2 * x 2) * x 1 ^ 2 + deriv P ρ * (2 * x 2) := by
      rw [g65c_cp _ _ _ d1]; apply HasDerivAt.deriv
      have H := ((g65c_K_line2 G _ (x 1) (x 2) hGd).mul_const (x 1 ^ 2)).add
        (g65c_K_line2 P _ (x 1) (x 2) hdPd.hasDerivAt)
      convert H using 1
      funext t; simp
    have C2 : cartesianPartial (fun y : V4 => -(G (y 1 ^ 2 + y 2 ^ 2) * (y 1 * y 2))) x 1 =
        -(deriv G ρ * (2 * x 1) * (x 1 * x 2) + G ρ * x 2) := by
      rw [g65c_cp _ _ _ d2]; apply HasDerivAt.deriv
      have hl : HasDerivAt (fun t : ℝ => (x 1 + t) * x 2) (x 2) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).const_add (x 1)).mul_const (x 2)
      have H := ((g65c_K_line G _ (x 1) (x 2) hGd).mul hl).neg
      convert H using 1
      · funext t; simp
      · simp [hρdef]
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [g65c_cp_const _ _ 0 (fun t => by simp [vortexStress, vortexFour, vortexGamma, vortexPressure, axisRadius]),
      g65c_cp_const _ _ 3 (fun t => by simp [vortexStress, vortexFour, minkowskiMetric]), e1, e2, C1, C2,
      hdP.deriv]
    simp only [hG, hP]
    field_simp
    ring
  · -- j = 3
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [g65c_cp_const _ _ 0 (fun t => by simp [vortexStress, vortexFour, minkowskiMetric]),
      g65c_cp_const _ _ 1 (fun t => by simp [vortexStress, vortexFour, minkowskiMetric]),
      g65c_cp_const _ _ 2 (fun t => by simp [vortexStress, vortexFour, minkowskiMetric]),
      g65c_cp_const _ _ 3 (fun t => by simp [vortexStress, vortexFour, minkowskiMetric, vortexPressure, axisRadius])]
    simp


theorem solution (c W rho : ℝ) (x : V4)
    (hc : 0 < c) (hW : 0 < W) (hrho : 0 < rho) (hx : 0 < axisRadius x) :
    (∀ j : Fin 4, (∑ i, cartesianPartial (fun y => vortexStress c W rho y i j) x i) = 0) ∧
    (∀ r : ℝ, 0 < r →
      deriv (vortexPressure c W rho) r =
        (rho * c ^ 2 + vortexPressure c W rho r) * W ^ 2 / (c ^ 2 * r ^ 3)) := by
  refine ⟨g65c_euler c W rho x hc hx, fun r hr => ?_⟩
  have hne : 2 * c ^ 2 * r ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => -W ^ 2 / (2 * c ^ 2 * s ^ 2)) (W ^ 2 / (c ^ 2 * r ^ 3)) r := by
    have := (hasDerivAt_const r (-W ^ 2)).fun_div ((hasDerivAt_pow 2 r).const_mul (2 * c ^ 2)) hne
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    field_simp; ring
  have := ((h1.exp).const_mul (rho * c ^ 2)).sub_const (rho * c ^ 2)
  have e : vortexPressure c W rho = fun s => rho * c ^ 2 * Real.exp (-W ^ 2 / (2 * c ^ 2 * s ^ 2)) - rho * c ^ 2 := by
    funext s; rfl
  rw [e, this.deriv]
  simp only
  ring
