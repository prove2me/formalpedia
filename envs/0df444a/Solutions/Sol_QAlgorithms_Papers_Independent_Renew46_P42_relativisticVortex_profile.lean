-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.relativisticVortex_profile
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:46:36.802145+00:00
-- url     : https://prove2.me/submissions/59865157-3a26-4869-a2c2-efc770bcba2b

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

theorem g64h_cp_const {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    (h : ∀ t : ℝ, f (x + t • Pi.single i 1) = f x) : cartesianPartial f x i = 0 := by
  by_cases hd : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y)) (WithLp.toLp 2 x)
  · have hf : DifferentiableAt ℝ f x := by
      have h2 : DifferentiableAt ℝ (fun z : Fin d → ℝ => WithLp.toLp 2 z) x :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.differentiableAt
      have := hd.comp x h2
      simpa [Function.comp_def] using this
    rw [g64h_cp f x i hf]
    simp [h]
  · simp [cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial,
      fderiv_zero_of_not_differentiableAt hd]

theorem g64h_inv_line (A c a b : ℝ) (h : 0 < a ^ 2 + b ^ 2) (hc : c ≠ 0) :
    HasDerivAt (fun t : ℝ => A / (c * ((a + t) ^ 2 + b ^ 2)))
      (-A * (c * (2 * a)) / (c * (a ^ 2 + b ^ 2)) ^ 2) 0 := by
  have hl : HasDerivAt (fun t : ℝ => a + t) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add a
  have hden : HasDerivAt (fun t : ℝ => c * ((a + t) ^ 2 + b ^ 2)) (c * (2 * (a + 0) * 1)) 0 := by
    simpa using ((hl.pow 2).add_const (b ^ 2)).const_mul c
  have hne : c * ((a + 0) ^ 2 + b ^ 2) ≠ 0 := by simpa using mul_ne_zero hc h.ne'
  have := (hasDerivAt_const (0:ℝ) A).fun_div hden hne
  refine this.congr_deriv ?_
  simp

theorem g64h_K_line (K : ℝ → ℝ) (K' a b : ℝ) (hK : HasDerivAt K K' (a ^ 2 + b ^ 2)) :
    HasDerivAt (fun t : ℝ => K ((a + t) ^ 2 + b ^ 2)) (K' * (2 * a)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => a + t) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add a
  have hin : HasDerivAt (fun t : ℝ => (a + t) ^ 2 + b ^ 2) (2 * a) 0 := by
    simpa using ((hl.pow 2).add_const (b ^ 2))
  have hK' : HasDerivAt K K' ((a + 0) ^ 2 + b ^ 2) := by simpa using hK
  exact hK'.comp 0 hin

theorem g64h_div6 (c W : ℝ) (x : V4) (hc : 0 < c) (hx : 0 < axisRadius x) :
    divergence4 (vortexFour c W) x = 0 := by
  have hR : ∀ y : V4, axisRadius y ^ 2 = y 1 ^ 2 + y 2 ^ 2 := fun y => by
    rw [axisRadius, Real.sq_sqrt (by positivity)]
  have hρ : 0 < x 1 ^ 2 + x 2 ^ 2 := by rw [← hR]; positivity
  have e1 : (fun y => vortexFour c W y 1) = fun y => (-W * y 2) / (c * (y 1 ^ 2 + y 2 ^ 2)) := by
    funext y; simp [vortexFour, hR]
  have e2 : (fun y => vortexFour c W y 2) = fun y => (W * y 1) / (c * (y 2 ^ 2 + y 1 ^ 2)) := by
    funext y; simp [vortexFour, hR, add_comm]
  have hd1 : DifferentiableAt ℝ (fun y : V4 => (-W * y 2) / (c * (y 1 ^ 2 + y 2 ^ 2))) x := by
    have : c * (x 1 ^ 2 + x 2 ^ 2) ≠ 0 := mul_ne_zero hc.ne' (by linarith)
    fun_prop (disch := exact this)
  have hd2 : DifferentiableAt ℝ (fun y : V4 => (W * y 1) / (c * (y 2 ^ 2 + y 1 ^ 2))) x := by
    have : c * (x 2 ^ 2 + x 1 ^ 2) ≠ 0 := mul_ne_zero hc.ne' (by linarith)
    fun_prop (disch := exact this)
  simp only [divergence4, Fin.sum_univ_four]
  rw [g64h_cp_const _ _ 0 (fun t => by simp [vortexFour, axisRadius]),
    g64h_cp_const _ _ 3 (fun t => by simp [vortexFour]), e1, e2,
    g64h_cp _ _ _ hd1, g64h_cp _ _ _ hd2]
  simp
  rw [(g64h_inv_line (-(W * x 2)) c (x 1) (x 2) hρ hc.ne').deriv,
    (g64h_inv_line (W * x 1) c (x 2) (x 1) (by linarith) hc.ne').deriv]
  ring

theorem g64h_div7 (c : ℝ) (v : ℝ → ℝ) (x : V4) (hc : 0 < c) (hx : 0 < axisRadius x)
    (hreg : DifferentiableAt ℝ v (axisRadius x)) (hv : |v (axisRadius x)| < c) :
    divergence4 (fun y => fourFlow c (circularFlow v y)) x = 0 := by
  set K : ℝ → ℝ := fun s => (1 / Real.sqrt (1 - (v (Real.sqrt s) / Real.sqrt s) ^ 2 * s / c ^ 2)) *
    (v (Real.sqrt s) / Real.sqrt s) / c with hKdef
  have hdot : ∀ y : V4, dot3 (circularFlow v y) (circularFlow v y) =
      (v (axisRadius y) / axisRadius y) ^ 2 * (y 1 ^ 2 + y 2 ^ 2) := by
    intro y; simp [dot3, circularFlow, Fin.sum_univ_three]; ring
  have e1 : (fun y => fourFlow c (circularFlow v y) 1) = fun y => K (y 1 ^ 2 + y 2 ^ 2) * (-y 2) := by
    funext y
    simp only [fourFlow, lorentzFactor, hdot, hKdef]
    simp [circularFlow, axisRadius]
    ring
  have e2 : (fun y => fourFlow c (circularFlow v y) 2) = fun y => K (y 2 ^ 2 + y 1 ^ 2) * y 1 := by
    funext y
    simp only [fourFlow, lorentzFactor, hdot, hKdef]
    simp [circularFlow, axisRadius, add_comm (y 2 ^ 2)]
    ring
  set ρ := x 1 ^ 2 + x 2 ^ 2 with hρdef
  have hRρ : axisRadius x = Real.sqrt ρ := rfl
  have hρ : 0 < ρ := by
    have := hx; rw [hRρ] at this; exact Real.sqrt_pos.1 this
  have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hds : DifferentiableAt ℝ Real.sqrt ρ := (Real.hasDerivAt_sqrt hρ.ne').differentiableAt
  have hdv : DifferentiableAt ℝ (fun s => v (Real.sqrt s)) ρ := by
    rw [hRρ] at hreg; exact hreg.comp ρ hds
  have hdq : DifferentiableAt ℝ (fun s => v (Real.sqrt s) / Real.sqrt s) ρ := hdv.div hds hsq.ne'
  have hargpos : 0 < 1 - (v (Real.sqrt ρ) / Real.sqrt ρ) ^ 2 * ρ / c ^ 2 := by
    have e : (v (Real.sqrt ρ) / Real.sqrt ρ) ^ 2 * ρ = v (Real.sqrt ρ) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hρ.le]; field_simp
    rw [e, sub_pos, div_lt_one (by positivity)]
    rw [hRρ] at hv
    have := sq_lt_sq' (abs_lt.1 hv).1 (abs_lt.1 hv).2
    linarith
  have hdarg : DifferentiableAt ℝ (fun s => 1 - (v (Real.sqrt s) / Real.sqrt s) ^ 2 * s / c ^ 2) ρ := by
    apply DifferentiableAt.sub (differentiableAt_const _)
    exact ((hdq.pow 2).mul differentiableAt_id).div_const _
  have hdK : DifferentiableAt ℝ K ρ := by
    have h1 := hdarg.sqrt hargpos.ne'
    have h2 := (differentiableAt_const (1:ℝ)).div h1 (Real.sqrt_pos.2 hargpos).ne'
    exact (h2.mul hdq).div_const c
  have hdK' : DifferentiableAt ℝ K (x 2 ^ 2 + x 1 ^ 2) := by rw [add_comm]; exact hdK
  have hd1 : DifferentiableAt ℝ (fun y : V4 => K (y 1 ^ 2 + y 2 ^ 2) * (-y 2)) x := by
    have : DifferentiableAt ℝ (fun y : V4 => K (y 1 ^ 2 + y 2 ^ 2)) x :=
      hdK.comp (f := fun y : V4 => y 1 ^ 2 + y 2 ^ 2) x (by fun_prop)
    exact this.mul (by fun_prop)
  have hd2 : DifferentiableAt ℝ (fun y : V4 => K (y 2 ^ 2 + y 1 ^ 2) * y 1) x := by
    have : DifferentiableAt ℝ (fun y : V4 => K (y 2 ^ 2 + y 1 ^ 2)) x :=
      hdK'.comp (f := fun y : V4 => y 2 ^ 2 + y 1 ^ 2) x (by fun_prop)
    exact this.mul (by fun_prop)
  simp only [divergence4, Fin.sum_univ_four]
  rw [g64h_cp_const _ _ 0 (fun t => by simp [fourFlow, circularFlow, axisRadius]),
    g64h_cp_const _ _ 3 (fun t => by simp [fourFlow, circularFlow]), e1, e2,
    g64h_cp _ _ _ hd1, g64h_cp _ _ _ hd2]
  simp
  have l1 := g64h_K_line K (deriv K ρ) (x 1) (x 2) hdK.hasDerivAt
  have l2 := g64h_K_line K (deriv K ρ) (x 2) (x 1) (by rw [add_comm]; exact hdK.hasDerivAt)
  rw [l1.deriv, l2.deriv]
  ring

/-- PDF p.8, (65)–(68), and (53): the relativistic circular flow is subluminal,
has the stated Lorentz factor, and obeys continuity off the excluded axis. -/
theorem solution (c W r : ℝ) (x : V4)
    (hc : 0 < c) (hW : 0 < W) (hr : 0 < r) (hx : 0 < axisRadius x) :
    0 < vortexSpeed c W r ∧ vortexSpeed c W r < c ∧
    1 / Real.sqrt (1 - (vortexSpeed c W r) ^ 2 / c ^ 2) = vortexGamma c W r ∧
    fourFlow c (vortexFlow c W x) = vortexFour c W x ∧
    quadratic minkowskiMetric (vortexFour c W x) = 1 ∧ divergence4 (vortexFour c W) x = 0 ∧
    (∀ v : ℝ → ℝ, DifferentiableAt ℝ v (axisRadius x) → |v (axisRadius x)| < c →
      divergence4 (fun y => fourFlow c (circularFlow v y)) x = 0) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hγsq : ∀ s : ℝ, 0 < s → vortexGamma c W s ^ 2 * (c ^ 2 * s ^ 2) = c ^ 2 * s ^ 2 + W ^ 2 := by
    intro s hs
    rw [vortexGamma, Real.sq_sqrt (by positivity)]; field_simp
  have hγp : ∀ s : ℝ, 0 < vortexGamma c W s := fun s => by
    rw [vortexGamma]; exact Real.sqrt_pos.2 (by positivity)
  have hA : ∀ s : ℝ, 0 < s → 1 - vortexSpeed c W s ^ 2 / c ^ 2 = 1 / vortexGamma c W s ^ 2 := by
    intro s hs
    have := hγsq s hs
    have := hγp s
    rw [vortexSpeed]; field_simp; linear_combination hγsq s hs
  have hinv : ∀ s : ℝ, 0 < s → 1 / Real.sqrt (1 - vortexSpeed c W s ^ 2 / c ^ 2) = vortexGamma c W s := by
    intro s hs
    have := hγp s
    rw [hA s hs, show (1:ℝ) / vortexGamma c W s ^ 2 = (1 / vortexGamma c W s) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    field_simp
  have hR : axisRadius x ^ 2 = x 1 ^ 2 + x 2 ^ 2 := by rw [axisRadius, Real.sq_sqrt (by positivity)]
  refine ⟨?_, ?_, hinv r hr, ?_, ?_, g64h_div6 c W x hc hx, fun v hv hvc => g64h_div7 c v x hc hx hv hvc⟩
  · rw [vortexSpeed]; have := hγp r; positivity
  · have h1 := hγsq r hr
    have h2 := hγp r
    rw [vortexSpeed, div_lt_iff₀ (by positivity)]
    have hp : 0 < c * (vortexGamma c W r * r) := by positivity
    by_contra hcon
    push Not at hcon
    nlinarith [mul_self_le_mul_self hp.le hcon, mul_pos hc2 (pow_pos hr 2)]
  · have hdot : dot3 (vortexFlow c W x) (vortexFlow c W x) = vortexSpeed c W (axisRadius x) ^ 2 := by
      simp only [dot3, vortexFlow, Fin.sum_univ_three]
      simp
      have hR0 : axisRadius x ≠ 0 := hx.ne'
      have : vortexSpeed c W (axisRadius x) / axisRadius x * x 2 * (vortexSpeed c W (axisRadius x) / axisRadius x * x 2) +
        vortexSpeed c W (axisRadius x) / axisRadius x * x 1 * (vortexSpeed c W (axisRadius x) / axisRadius x * x 1) =
        (vortexSpeed c W (axisRadius x) / axisRadius x) ^ 2 * axisRadius x ^ 2 := by rw [hR]; ring
      rw [this, div_pow]; field_simp
    have hlf : lorentzFactor c (vortexFlow c W x) = vortexGamma c W (axisRadius x) := by
      rw [lorentzFactor, hdot, hinv _ hx]
    have hγx := hγp (axisRadius x)
    ext i
    fin_cases i <;> simp only [fourFlow, vortexFour, hlf] <;> simp [vortexFlow, vortexSpeed] <;> field_simp
  · have := hγsq _ hx
    simp only [quadratic, Fin.sum_univ_four, minkowskiMetric, vortexFour]
    simp
    rw [hR] at this
    have hρ : 0 < x 1 ^ 2 + x 2 ^ 2 := by rw [← hR]; positivity
    field_simp
    linear_combination (x 1 ^ 2 + x 2 ^ 2) * this +
      (vortexGamma c W (axisRadius x) ^ 2 * c ^ 2 - c ^ 2) * (axisRadius x ^ 2 + x 1 ^ 2 + x 2 ^ 2) * hR


end

