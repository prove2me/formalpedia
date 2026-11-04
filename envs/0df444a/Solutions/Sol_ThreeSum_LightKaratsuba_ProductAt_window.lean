-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.ProductAt.window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:15.007552+00:00
-- url     : https://prove2.me/submissions/b86c4c6c-74c4-4270-a59e-af3b6cb752b1

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_Karatsuba_product_coeff_zero


set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.LightKaratsuba
namespace ProductAt
theorem _root_.solution {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (offset j : ℕ) :
    window (fun i => μ (out + i)) offset (2 * n) j =
      (X ^ offset * (asPolynomial as * asPolynomial bs)).coeff j := by
  rw [Polynomial.coeff_X_pow_mul']
  unfold ThreeSum.LightKaratsuba.window
  by_cases ho : offset ≤ j
  · rw [if_pos ho]
    by_cases hj : j < offset + 2 * n
    · rw [if_pos ⟨ho, hj⟩]
      exact hp _ (by omega)
    · rw [if_neg (by omega : ¬ (offset ≤ j ∧ j < offset + 2 * n))]
      exact (product_coeff_zero ha hb (by omega : 2 * n ≤ j - offset)).symm
  · rw [if_neg ho, if_neg (by omega : ¬ (offset ≤ j ∧ j < offset + 2 * n))]
end ProductAt
end ThreeSum.LightKaratsuba
