-- Prove2me | solution 1 for SpecActions.expected_saving_per_hit
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T04:39:18.224991+00:00
-- url     : https://prove2.me/submissions/597230f4-bce4-413d-a6e9-4e7b71255dba

import Mathlib
import Definitions.Def_SpecActions_model

open Filter Topology MeasureTheory Set

/-- Antiderivative of the outer integrand. -/
private noncomputable def HH (α β b : ℝ) : ℝ :=
  (-1) * (b * Real.exp (-β * b)) + (-1 / β + 1 / α) * Real.exp (-β * b)
    - (β / (α * (α + β))) * Real.exp (-(α + β) * b)

private theorem HH_eq (α β : ℝ) : HH α β = fun b : ℝ =>
    (-1) * (b * Real.exp (-β * b)) + (-1 / β + 1 / α) * Real.exp (-β * b)
      - (β / (α * (α + β))) * Real.exp (-(α + β) * b) := rfl

private theorem hasDerivAt_exp_lin (c x : ℝ) :
    HasDerivAt (fun b : ℝ => Real.exp (c * b)) (Real.exp (c * x) * c) x := by
  have h : HasDerivAt (fun b : ℝ => c * b) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  simpa using h.exp

private theorem tendsto_exp_lin (c : ℝ) (hc : 0 < c) :
    Tendsto (fun b : ℝ => Real.exp (-c * b)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun b : ℝ => -c * b) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by linarith : (-c : ℝ) < 0) tendsto_id
  simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h2

private theorem tendsto_id_mul_exp_lin (c : ℝ) (hc : 0 < c) :
    Tendsto (fun b : ℝ => b * Real.exp (-c * b)) atTop (𝓝 0) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have base : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h1 : Tendsto (fun b : ℝ => c * b) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have h3 := (base.comp h1).const_mul (1 / c)
  have hfe : (fun b : ℝ => (1 / c) * (((fun u : ℝ => u * Real.exp (-u)) ∘ fun b : ℝ => c * b) b))
      = fun b : ℝ => b * Real.exp (-c * b) := by
    funext b
    simp only [Function.comp_apply, neg_mul]
    field_simp
  rw [hfe] at h3
  simpa using h3

/-- The inner integral: the expected saving conditioned on the actor latency `b`. -/
private theorem inner_integral (α : ℝ) (hα : 0 < α) (b : ℝ) :
    (∫ a in (0 : ℝ)..b, (b - a) * (α * Real.exp (-α * a)))
      = b - (1 - Real.exp (-α * b)) / α := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have key : ∀ a : ℝ,
      HasDerivAt (fun a : ℝ => Real.exp (-α * a) * (1 / α - b + a))
        ((b - a) * (α * Real.exp (-α * a))) a := by
    intro a
    have h1 : HasDerivAt (fun a : ℝ => Real.exp (-α * a)) (Real.exp (-α * a) * (-α)) a :=
      hasDerivAt_exp_lin (-α) a
    have h2 : HasDerivAt (fun a : ℝ => 1 / α - b + a) 1 a := by
      simpa using (hasDerivAt_id a).const_add (1 / α - b)
    have h3 := h1.mul h2
    have heq : (b - a) * (α * Real.exp (-α * a))
        = Real.exp (-α * a) * (-α) * (1 / α - b + a) + Real.exp (-α * a) * 1 := by
      field_simp
      try ring
    rw [heq]
    exact h3
  have hint : IntervalIntegrable (fun a : ℝ => (b - a) * (α * Real.exp (-α * a)))
      MeasureTheory.volume 0 b := (by fun_prop : Continuous _).intervalIntegrable 0 b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => key a) hint]
  simp only [mul_zero, Real.exp_zero, one_mul, add_zero, sub_add_cancel]
  field_simp
  try ring

theorem solution (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∫ b in Set.Ioi (0 : ℝ),
        (∫ a in (0 : ℝ)..b, (b - a) * (α * Real.exp (-α * a)))
          * (β * Real.exp (-β * b))
      = α / (β * (α + β)) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hab : (0 : ℝ) < α + β := by linarith
  have habne : α + β ≠ 0 := ne_of_gt hab
  simp only [inner_integral α hα]
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (HH α β)
        ((x - (1 - Real.exp (-α * x)) / α) * (β * Real.exp (-β * x))) x := by
    intro x _
    have d1 : HasDerivAt (fun b : ℝ => Real.exp (-β * b)) (Real.exp (-β * x) * (-β)) x :=
      hasDerivAt_exp_lin (-β) x
    have d2 : HasDerivAt (fun b : ℝ => Real.exp (-(α + β) * b))
        (Real.exp (-(α + β) * x) * (-(α + β))) x := hasDerivAt_exp_lin (-(α + β)) x
    have d3 : HasDerivAt (fun b : ℝ => b * Real.exp (-β * b))
        (1 * Real.exp (-β * x) + x * (Real.exp (-β * x) * (-β))) x :=
      (hasDerivAt_id x).mul d1
    have hsplit : Real.exp (-(α + β) * x) = Real.exp (-α * x) * Real.exp (-β * x) := by
      rw [← Real.exp_add]; ring_nf
    have heq : (x - (1 - Real.exp (-α * x)) / α) * (β * Real.exp (-β * x))
        = (-1 : ℝ) * (1 * Real.exp (-β * x) + x * (Real.exp (-β * x) * (-β)))
          + (-1 / β + 1 / α) * (Real.exp (-β * x) * (-β))
          - (β / (α * (α + β))) * (Real.exp (-(α + β) * x) * (-(α + β))) := by
      rw [hsplit]
      field_simp
      try ring
    rw [heq, HH_eq]
    exact ((d3.const_mul (-1 : ℝ)).add (d1.const_mul (-1 / β + 1 / α))).sub
      (d2.const_mul (β / (α * (α + β))))
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 ≤ (x - (1 - Real.exp (-α * x)) / α) * (β * Real.exp (-β * x)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hexp : 1 - α * x ≤ Real.exp (-α * x) := by
      have := Real.add_one_le_exp (-α * x)
      linarith
    have h1 : 0 ≤ x - (1 - Real.exp (-α * x)) / α := by
      rw [sub_nonneg, div_le_iff₀ hα]
      linarith
    have h2 : 0 ≤ β * Real.exp (-β * x) := by positivity
    exact mul_nonneg h1 h2
  have hlim : Tendsto (HH α β) atTop (𝓝 0) := by
    have e1 := tendsto_id_mul_exp_lin β hβ
    have e2 := tendsto_exp_lin β hβ
    have e3 := tendsto_exp_lin (α + β) hab
    have h := ((e1.const_mul (-1 : ℝ)).add (e2.const_mul (-1 / β + 1 / α))).sub
      (e3.const_mul (β / (α * (α + β))))
    rw [HH_eq]
    simpa using h
  have main : ∫ b in Set.Ioi (0 : ℝ),
      (b - (1 - Real.exp (-α * b)) / α) * (β * Real.exp (-β * b)) = 0 - HH α β 0 :=
    integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  rw [main, HH_eq]
  norm_num
  field_simp
  try ring

