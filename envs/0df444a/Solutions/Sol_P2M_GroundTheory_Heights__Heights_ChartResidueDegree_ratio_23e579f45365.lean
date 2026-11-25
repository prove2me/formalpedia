-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartResidueDegree_ratio_23e579f45365
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:51.544794+00:00
-- url     : https://prove2.me/submissions/1dfa4026-2f8b-42ac-933d-26ede20661a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartResidueDegree
namespace GroundTheory.Heights₂.Heights.ChartResidueDegree
theorem _root_.solution {K σ : Type*} [Field K] {n : ℕ} (ξ τ : Fin n → K) (A : Fin n → MvPolynomial σ K)
    (B : MvPolynomial σ K) (ℓ' : K) (hB : B ≠ 0) (hℓ : ∑ l, τ l * ξ l ≠ 0)
    (hrel : ∀ m, A m * C ℓ' = B * C (ξ m)) :
    ∑ l, C (τ l) * A l ≠ 0 ∧ ∀ m, A m = C (ξ m / ∑ l, τ l * ξ l) * ∑ l, C (τ l) * A l := by
  set ℓ := ∑ l, τ l * ξ l
  have hCℓ : (C ℓ : MvPolynomial σ K) ≠ 0 := by rwa [Ne, C_eq_zero]
  have hsum : (∑ l, C (τ l) * A l) * C ℓ' = B * C ℓ := by
    calc (∑ l, C (τ l) * A l) * C ℓ' = ∑ l, C (τ l) * (A l * C ℓ') := by
          rw [Finset.sum_mul]; simp only [mul_assoc]
      _ = ∑ l, B * C (τ l * ξ l) := Finset.sum_congr rfl fun l _ => by rw [hrel l, C_mul]; ring
      _ = B * C ℓ := by rw [← Finset.mul_sum, ← map_sum]
  have hprod : (∑ l, C (τ l) * A l) * C ℓ' ≠ 0 := by rw [hsum]; exact mul_ne_zero hB hCℓ
  refine ⟨left_ne_zero_of_mul hprod, fun m => ?_⟩
  have hηC : C (ξ m / ℓ) * C ℓ = (C (ξ m) : MvPolynomial σ K) := by rw [← C_mul, div_mul_cancel₀ _ hℓ]
  apply mul_right_cancel₀ (mul_ne_zero (right_ne_zero_of_mul hprod) hCℓ)
  linear_combination (C ℓ) * hrel m - (C (ξ m / ℓ) * C ℓ) * hsum - (B * C ℓ) * hηC
end GroundTheory.Heights₂.Heights.ChartResidueDegree
