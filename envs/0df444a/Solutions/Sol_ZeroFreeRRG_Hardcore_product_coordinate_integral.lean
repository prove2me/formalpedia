-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.product_coordinate_integral
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:04:32.763986+00:00
-- url     : https://prove2.me/submissions/b01e5214-2af8-483c-92dd-1407af08e15e

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical BigOperators

theorem solution (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : Fin d → ℝ → ℝ) (b : ℝ → ℝ) (i : Fin d) :
    (∫ xs : Fin d → ℝ, (∏ j, a j (xs j)) * b (xs i)
       ∂(Measure.pi fun _ : Fin d => μ)) =
      (∫ x, a i x * b x ∂μ) * ∏ j ∈ Finset.univ.erase i, (∫ x, a j x ∂μ) := by
  let f := fun j : Fin d => fun x : ℝ => a j x * if j=i then b x else 1
  have heq (xs : Fin d → ℝ) : (∏ j, f j (xs j)) = (∏ j, a j (xs j))*b (xs i) := by
    dsimp [f]
    rw [Finset.prod_mul_distrib]
    simp
  have hint : (∫ xs : Fin d → ℝ, (∏ j, a j (xs j))*b (xs i) ∂(Measure.pi fun _ : Fin d => μ)) =
      ∏ j, ∫ x, f j x ∂μ := by
    rw [← integral_fintype_prod_eq_prod f]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun xs => (heq xs).symm)
  rw [hint]
  have hprod := Finset.prod_erase_mul Finset.univ (fun j : Fin d => ∫ x, f j x ∂μ) (Finset.mem_univ i)
  rw [← hprod]
  have hrest : (∏ j ∈ Finset.univ.erase i, ∫ x, f j x ∂μ) =
      ∏ j ∈ Finset.univ.erase i, ∫ x, a j x ∂μ := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [f,hji]
  rw [hrest]
  simp [f, mul_comm]
