-- Prove2me | solution 1 for SAARate.SharpLD.cgf_deriv_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:02:52.459986+00:00
-- url     : https://prove2.me/submissions/8b496940-1ca2-4f33-9662-41163f888f81

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    Differentiable ℝ (cgf X P) ∧
      ∀ t : ℝ, deriv (cgf X P) t = (∫ ω, X ω * Real.exp (t * X ω) ∂P) / mgf X P t ∧
        |deriv (cgf X P) t| ≤ κ := by
  have hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (-κ) κ := by
    filter_upwards [hXκ] with ω hω
    exact abs_le.mp hω
  have hi (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) P :=
    integrable_exp_mul_of_mem_Icc hX.aemeasurable hb
  have hs : integrableExpSet X P = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact hi t
  have ht (t : ℝ) : t ∈ interior (integrableExpSet X P) := by simp [hs]
  refine ⟨fun t => (analyticAt_cgf (ht t)).differentiableAt, ?_⟩
  intro t
  refine ⟨deriv_cgf (ht t), ?_⟩
  rw [deriv_cgf (ht t), abs_div, abs_of_pos (mgf_pos (hi t))]
  apply (div_le_iff₀ (mgf_pos (hi t))).2
  have hj : Integrable (fun ω => X ω * Real.exp (t * X ω)) P := by
    simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet (ht t) 1
  calc
    |∫ ω, X ω * Real.exp (t * X ω) ∂P| ≤
        ∫ ω, |X ω * Real.exp (t * X ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, κ * Real.exp (t * X ω) ∂P := by
      apply integral_mono_ae hj.abs ((hi t).const_mul κ)
      filter_upwards [hXκ] with ω hω
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right hω (le_of_lt (Real.exp_pos _))
    _ = κ * mgf X P t := by rw [integral_const_mul]; rfl

#print axioms solution
