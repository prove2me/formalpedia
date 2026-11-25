-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_prod_fact_mul_fact_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:35.689348+00:00
-- url     : https://prove2.me/submissions/e082453e-88e2-48f7-aea7-28308a2c096d

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) :
    (∏ i, (a i).factorial) * D.factorial ≤ ((∑ i, a i) + D).factorial := by
  have h1 : (∏ i, (a i).factorial) ∣ (∑ i, a i).factorial := by
    first
      | exact Nat.prod_factorial_dvd_factorial_sum _ _
      | exact Nat.prod_factorial_dvd_factorial_sum
  have h2 : (∑ i, a i).factorial * D.factorial ∣ ((∑ i, a i) + D).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
  exact Nat.le_of_dvd (Nat.factorial_pos _) (dvd_trans (mul_dvd_mul_right h1 _) h2)
end ReciprocityTheory.GeometryOfNumbersTheory
