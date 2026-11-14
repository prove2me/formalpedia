-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.centered_product_coordinate_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:06:57.12435+00:00
-- url     : https://prove2.me/submissions/b809481d-8029-4765-bee2-81ea5550be43

import Theorems.Thm_ZeroFreeRRG_Hardcore_product_coordinate_integral
import Mathlib
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hint : Integrable (fun x : ℝ => x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 0) (φ : ℝ → ℝ) (i j : Fin d) :
    (∫ xs : Fin d → ℝ, ((∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) * φ (xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) = if i=j then (∫ x, x*φ x ∂μ) else 0 := by
  let A := fun x : ℝ => 1+θ*x
  let a := fun k : Fin d => fun x : ℝ => if k=j then x else A x
  have hA : (∫ x, A x ∂μ) = 1 := by
    dsimp [A]
    rw [integral_add (integrable_const 1) (hint.const_mul θ),integral_const_mul]
    simp [hmean]
  have hprod (xs : Fin d → ℝ) : (∏ k, a k (xs k)) =
      (∏ k ∈ Finset.univ.erase j, A (xs k))*xs j := by
    rw [← Finset.prod_erase_mul Finset.univ (fun k => a k (xs k)) (Finset.mem_univ j)]
    have hrest : (∏ k ∈ Finset.univ.erase j, a k (xs k)) =
        ∏ k ∈ Finset.univ.erase j, A (xs k) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk' : k ≠ j := (Finset.mem_erase.mp hk).1
      simp [a,hk']
    rw [hrest]
    simp [a]
  have heq : (∫ xs : Fin d → ℝ, ((∏ k ∈ Finset.univ.erase j, A (xs k))*xs j) * φ (xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) =
      (∫ x, a i x * φ x ∂μ) * ∏ k ∈ Finset.univ.erase i, (∫ x, a k x ∂μ) := by
    calc
      _ = ∫ xs : Fin d → ℝ, (∏ k, a k (xs k)) * φ (xs i) ∂(Measure.pi fun _ : Fin d => μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun xs => by simp only [hprod])
      _ = _ := product_coordinate_integral d μ a φ i
  rw [heq]
  by_cases hij : i=j
  · subst i
    have hr : (∏ k ∈ Finset.univ.erase j, ∫ x, a k x ∂μ) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      have hk' : k ≠ j := (Finset.mem_erase.mp hk).1
      simpa [a,hk'] using hA
    simp [a,hr]
  · have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij,Finset.mem_univ j⟩
    have hr : (∏ k ∈ Finset.univ.erase i, ∫ x, a k x ∂μ) = 0 := by
      apply Finset.prod_eq_zero hj
      simpa [a] using hmean
    simp [hij,hr]
