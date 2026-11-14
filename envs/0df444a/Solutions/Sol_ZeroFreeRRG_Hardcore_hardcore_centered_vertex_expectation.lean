-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_centered_vertex_expectation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:20:16.570757+00:00
-- url     : https://prove2.me/submissions/e465951b-5ee1-4baa-929f-255203775cb5

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_centered
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (α : ℝ) (ha : 0 < α) (ha1 : α < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α) :
    let η := Measure.map (fun x : Fin 2 → ℝ => (x 1-α)/(1-α)) (ν : Measure (Fin 2 → ℝ))
    (∫ xs : Fin d → Fin 2 → ℝ, xlogx (vertexFactor .hardcore α d xs)
      ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin 2 → ℝ)))) =
    ∫ hs : Fin d → ℝ,
      let V := ((∏ i, (1+(α/(1-α))*hs i)) + (α/(1-α))*(∏ i, (1-hs i)))/(1+α/(1-α))
      V * Real.log V ∂(Measure.pi fun _ : Fin d => η) := by
  dsimp only
  let C := fun x : Fin 2 → ℝ => (x 1-α)/(1-α)
  let η := Measure.map C (ν : Measure (Fin 2 → ℝ))
  let T := fun xs : Fin d → Fin 2 → ℝ => fun i => C (xs i)
  let μ := Measure.pi fun _ : Fin d => (ν : Measure (Fin 2 → ℝ))
  let K := fun hs : Fin d → ℝ =>
    let V := ((∏ i, (1+(α/(1-α))*hs i)) + (α/(1-α))*(∏ i, (1-hs i)))/(1+α/(1-α))
    V * Real.log V
  have hc : Measurable C := by dsimp [C]; fun_prop
  letI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hc.aemeasurable
  have hT : Measurable T := by
    apply measurable_pi_lambda
    intro i
    exact hc.comp (measurable_pi_apply i)
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hmap : Measure.map T μ = Measure.pi (fun _ : Fin d => η) := by
    exact Measure.pi_map_pi (fun _ => hc.aemeasurable)
  have hs : ∀ᵐ xs ∂μ, ∀ i, (∑ a, xs i a) = 1 := by
    have hv : ∀ᵐ x ∂(ν : Measure (Fin 2 → ℝ)), x ∈ stdSimplex ℝ (Fin 2) := by
      apply ae_iff.mpr
      exact hν.1
    have hv' : ∀ᵐ x ∂(ν : Measure (Fin 2 → ℝ)), (∑ a, x a)=1 := by
      filter_upwards [hv] with x hx
      exact hx.2
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => hv')
  change (∫ xs, xlogx (vertexFactor .hardcore α d xs) ∂μ) = ∫ hs, K hs ∂(Measure.pi fun _ : Fin d => η)
  rw [← hmap,integral_map hT.aemeasurable hK.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hs] with xs hx
  have hh := hardcore_vertex_centered d α ha ha1 xs hx
  dsimp [K,T,C,xlogx]
  rw [hh]
