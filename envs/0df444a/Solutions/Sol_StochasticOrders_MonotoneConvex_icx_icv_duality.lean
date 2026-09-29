-- Prove2me | solution 1 for StochasticOrders.MonotoneConvex.icx_icv_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:02:16.940606+00:00
-- url     : https://prove2.me/submissions/80b29289-ac50-4376-9bab-8daac1e84ef5

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory

theorem aux_icxdual_mono {φ : ℝ → ℝ} (h : Monotone φ) : Monotone (fun x => -φ (-x)) := by
  intro x y hxy
  have := h (neg_le_neg hxy)
  simp only
  linarith

theorem aux_icxdual_cvx {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ConcaveOn ℝ Set.univ (fun x => -φ (-x)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have := hφ.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at *
  have e : -(a * x + b * y) = a * (-x) + b * (-y) := by ring
  rw [e]
  linarith

theorem aux_icxdual_ccv {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) :
    ConvexOn ℝ Set.univ (fun x => -φ (-x)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have := hφ.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at *
  have e : -(a * x + b * y) = a * (-x) + b * (-y) := by ring
  rw [e]
  linarith

end StochasticOrders.MonotoneConvex

open StochasticOrders.MonotoneConvex
open MeasureTheory

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) :
    (IcxOrder μ ν X Y ↔ IcvOrder ν μ (fun ω => -(Y ω)) (fun ω => -(X ω))) ∧
    (IcvOrder μ ν X Y ↔ IcxOrder ν μ (fun ω => -(Y ω)) (fun ω => -(X ω))) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · intro ψ hm hc hiY hiX
    have hX : Integrable ((fun x => -ψ (-x)) ∘ X) μ := hiX.neg
    have hY : Integrable ((fun x => -ψ (-x)) ∘ Y) ν := hiY.neg
    have := h _ (aux_icxdual_mono hm) (aux_icxdual_ccv hc) hX hY
    simp only [integral_neg] at this
    linarith
  · intro φ hm hc hiX hiY
    have hY : Integrable ((fun x => -φ (-x)) ∘ fun ω => -(Y ω)) ν := by
      simpa [Function.comp_def] using hiY.neg
    have hX : Integrable ((fun x => -φ (-x)) ∘ fun ω => -(X ω)) μ := by
      simpa [Function.comp_def] using hiX.neg
    have := h _ (aux_icxdual_mono hm) (aux_icxdual_cvx hc) hY hX
    simp only [neg_neg, integral_neg] at this
    linarith
  · intro ψ hm hc hiY hiX
    have hX : Integrable ((fun x => -ψ (-x)) ∘ X) μ := hiX.neg
    have hY : Integrable ((fun x => -ψ (-x)) ∘ Y) ν := hiY.neg
    have := h _ (aux_icxdual_mono hm) (aux_icxdual_cvx hc) hX hY
    simp only [integral_neg] at this
    linarith
  · intro φ hm hc hiX hiY
    have hY : Integrable ((fun x => -φ (-x)) ∘ fun ω => -(Y ω)) ν := by
      simpa [Function.comp_def] using hiY.neg
    have hX : Integrable ((fun x => -φ (-x)) ∘ fun ω => -(X ω)) μ := by
      simpa [Function.comp_def] using hiX.neg
    have := h _ (aux_icxdual_mono hm) (aux_icxdual_ccv hc) hY hX
    simp only [neg_neg, integral_neg] at this
    linarith
