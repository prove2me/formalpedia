-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_strict_derivative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:13:16.724838+00:00
-- url     : https://prove2.me/submissions/3be752cf-2ea8-439d-bf06-b517b5c540b2

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_log_product_cancellation
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_mean_zero
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_log_split
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_factorization
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_tilted_gradient_positive
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_entropy_integral_derivative
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (hd : 2 ≤ d) (η : Measure ℝ) [IsProbabilityMeasure η]
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hint : Integrable (fun h : ℝ => h) η)
    (hmean : (∫ h : ℝ, h ∂η) = 0) (hn : ¬(∀ᵐ h ∂η, h=0)) :
    0 < deriv (fun t : ℝ => ∫ hs : Fin d → ℝ,
      let V := ((∏ i, (1+t*hs i)) + t*(∏ i, (1-hs i)))/(1+t)
      V * Real.log V ∂(Measure.pi fun _ : Fin d => η)) θ := by
  let ν := Measure.pi fun _ : Fin d => η
  let cube : Set (Fin d → ℝ) := Set.pi univ (fun _ => Icc (-1:ℝ) 1)
  let U := fun xs : Fin d → ℝ => (1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k)
  let W := fun xs : Fin d → ℝ => fun i => (1-xs i)/(1+θ*xs i)
  let L := fun xs : Fin d → ℝ => ∑ i, Real.log (1+θ*xs i)
  let Z := fun xs : Fin d → ℝ => Real.log (1+θ*∏ i, W xs i)
  let P := fun xs : Fin d → ℝ => ∏ i, (1+θ*xs i)
  let V := fun xs : Fin d → ℝ => (P xs + θ*(∏ i, (1-xs i)))/(1+θ)
  let E := fun xs : Fin d → ℝ => U xs/(1+θ)^2 * (Real.log (V xs)+1)
  have hcube : IsCompact cube := isCompact_univ_pi fun _ : Fin d => isCompact_Icc
  have hgood : ∀ᵐ xs ∂ν, xs ∈ cube := by
    have hh : ∀ᵐ xs ∂ν, ∀ i, -1 ≤ xs i ∧ xs i ≤ 1 := by
      apply Measure.ae_pi_le_pi
      exact Filter.eventually_pi (fun _ : Fin d => hb)
    filter_upwards [hh] with xs hx
    exact fun i hi => hx i
  have hci (F : (Fin d → ℝ) → ℝ) (hm : Measurable F) (hc : ContinuousOn F cube) : Integrable F ν := by
    obtain ⟨B,hB⟩ := hcube.exists_bound_of_continuousOn hc
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards [hgood] with xs hx
    exact hB xs hx
  have hpos (xs : Fin d → ℝ) (hx : xs ∈ cube) (i : Fin d) : 0 < 1+θ*xs i := by
    have hh := hx i (mem_univ i)
    nlinarith [mul_nonneg hθ.le (show 1+xs i ≥ 0 by linarith [hh.1])]
  have hUc : Continuous U := by dsimp [U]; fun_prop
  have hWc (i : Fin d) : ContinuousOn (fun xs => W xs i) cube := by
    dsimp [W]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro xs hx
    exact ne_of_gt (hpos xs hx i)
  have hWprod : ContinuousOn (fun xs => ∏ i, W xs i) cube := by
    apply continuousOn_finsetProd
    intro i hi
    exact hWc i
  have hZc : ContinuousOn Z cube := by
    dsimp [Z]
    apply ContinuousOn.log (continuousOn_const.add (continuousOn_const.mul hWprod))
    intro xs hx
    have hnon (i : Fin d) : 0 ≤ W xs i := by
      dsimp [W]
      exact div_nonneg (by linarith [(hx i (mem_univ i)).2]) (hpos xs hx i).le
    have hp : 0 ≤ ∏ i, W xs i := Finset.prod_nonneg (fun i _ => hnon i)
    have : 0 < 1+θ*∏ i, W xs i := by nlinarith [mul_nonneg hθ.le hp]
    exact ne_of_gt this
  have hLc : ContinuousOn L cube := by
    dsimp [L]
    apply continuousOn_finsetSum
    intro i hi
    apply ContinuousOn.log (by fun_prop)
    intro xs hx
    exact ne_of_gt (hpos xs hx i)
  have hUi : Integrable U ν := hci U (by dsimp [U]; fun_prop) hUc.continuousOn
  have hULi : Integrable (fun xs => U xs*L xs) ν :=
    hci _ (by dsimp [U,L]; fun_prop) (hUc.continuousOn.mul hLc)
  have hUZi : Integrable (fun xs => U xs*Z xs) ν :=
    hci _ (by dsimp [U,Z,W]; fun_prop) (hUc.continuousOn.mul hZc)
  have hU0 : (∫ xs, U xs ∂ν) = 0 := hardcore_gradient_mean_zero d (by omega) η θ hb hint hmean
  have hUL0 : (∫ xs, U xs * L xs ∂ν) = 0 :=
    hardcore_gradient_log_product_cancellation d η θ hθ.le hθ1 hb hint hmean
  have hposInt : 0 < (∫ xs, U xs * Z xs ∂ν) := by
    have hp := hardcore_tilted_gradient_positive d hd η θ hθ hθ1 hb hint hmean hn
    have heq : (∫ xs, U xs * Z xs ∂ν) =
      ∫ xs, P xs * (((∏ i, W xs i)-∑ i, W xs i+d-1)*Z xs) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hgood] with xs hx
      have hden (i : Fin d) : 1+θ*xs i ≠ 0 := ne_of_gt (hpos xs hx i)
      have hh := hardcore_gradient_factorization d xs θ hden
      change U xs = P xs*((∏ i, W xs i)-∑ i, W xs i+d-1) at hh
      rw [hh]
      ring
    rw [heq]
    exact hp
  have hsplit : ∀ᵐ xs ∂ν, E xs = ((U xs*L xs + U xs*Z xs) + (1-Real.log (1+θ))*U xs)/(1+θ)^2 := by
    filter_upwards [hgood] with xs hx
    have hh := hardcore_vertex_log_split d xs θ hθ.le hθ1 (fun i => hx i (mem_univ i))
    change Real.log (V xs) = L xs + Z xs - Real.log (1+θ) at hh
    dsimp [E]
    rw [hh]
    ring
  have hintEq : (∫ xs, E xs ∂ν) = (∫ xs, U xs*Z xs ∂ν)/(1+θ)^2 := by
    rw [integral_congr_ae hsplit,integral_div]
    have hA : Integrable (fun xs => U xs*L xs + U xs*Z xs) ν := hULi.add hUZi
    have hB : Integrable (fun xs => (1-Real.log (1+θ))*U xs) ν := hUi.const_mul _
    rw [integral_add hA hB,integral_add hULi hUZi,integral_const_mul,hUL0,hU0]
    ring
  have hder := hardcore_entropy_integral_derivative d η hb θ hθ hθ1
  change HasDerivAt (fun t : ℝ => ∫ hs : Fin d → ℝ,
      let v := ((∏ i, (1+t*hs i)) + t*(∏ i, (1-hs i)))/(1+t)
      v * Real.log v ∂ν) (∫ xs, E xs ∂ν) θ at hder
  rw [hder.deriv, hintEq]
  exact div_pos hposInt (sq_pos_of_pos (by linarith))
