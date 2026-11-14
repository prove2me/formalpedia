-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_gradient_factorization
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:00:11.114344+00:00
-- url     : https://prove2.me/submissions/bb666d3a-e46e-4de0-980f-cfd1454c944b

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution (d : ℕ) (h : Fin d → ℝ) (θ : ℝ)
    (hden : ∀ i, 1+θ*h i ≠ 0) :
    let P := ∏ i, (1+θ*h i)
    let Q := ∏ i, (1-h i)
    let W := fun i => (1-h i)/(1+θ*h i)
    (1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) + Q - P =
      P*((∏ i, W i) - ∑ i, W i + d - 1) := by
  dsimp only
  let A := fun i : Fin d => 1+θ*h i
  let P := ∏ i, A i
  let Q := ∏ i, (1-h i)
  let W := fun i => (1-h i)/A i
  have hp : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hden i)
  have hP (i : Fin d) : (∏ j ∈ Finset.univ.erase i, A j) * A i = P := by
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have hWprod : P * (∏ i, W i) = Q := by
    dsimp [W]
    rw [Finset.prod_div_distrib]
    change P * (Q / P) = Q
    field_simp
  have hterm (i : Fin d) : (1+θ)*((∏ j ∈ Finset.univ.erase i, A j)*h i) = P - P*W i := by
    dsimp [W]
    rw [← hP i]
    have ha : A i ≠ 0 := hden i
    field_simp
    dsimp [A]
    ring
  have hsum : (1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, A j)*h i) =
      (d:ℝ)*P-P*(∑ i, W i) := by
    rw [Finset.mul_sum]
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  change (1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, A j)*h i)+Q-P =
    P*((∏ i, W i)-∑ i, W i+d-1)
  rw [hsum, ← hWprod]
  ring
