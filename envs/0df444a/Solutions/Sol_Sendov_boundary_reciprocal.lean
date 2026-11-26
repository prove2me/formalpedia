-- Prove2me | solution 1 for Sendov.boundary_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:04.670035+00:00
-- url     : https://prove2.me/submissions/7984eabe-8aa9-410e-a1b6-b9db6a591266

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
import Theorems.Thm_Sendov_prod_mul_sum_inv


set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {n : ℕ} {Zs Qi : Multiset ℂ} (hn0 : (n : ℂ) ≠ 0)
    (hZ : ∀ u ∈ Zs, u ≠ 0) (hQ : ∀ u ∈ Qi, u ≠ 0)
    (hI : Zs.prod = (n : ℂ) * Qi.prod)
    (hII : 2 * sumEraseProd Zs = (n : ℂ) * sumEraseProd Qi) :
    (Qi.map (fun u => u⁻¹)).sum = 2 * (Zs.map (fun u => u⁻¹)).sum := by
  have hQ0 : Qi.prod ≠ 0 := Multiset.prod_ne_zero fun h => hQ 0 h rfl
  have h1 := prod_mul_sum_inv Zs hZ
  have h2 := prod_mul_sum_inv Qi hQ
  have h : (n : ℂ) * Qi.prod * (2 * (Zs.map (fun u => u⁻¹)).sum)
      = (n : ℂ) * Qi.prod * (Qi.map (fun u => u⁻¹)).sum := by
    linear_combination (-2 * (Zs.map (fun u => u⁻¹)).sum) * hI + 2 * h1 + hII - (n : ℂ) * h2
  exact (mul_left_cancel₀ (mul_ne_zero hn0 hQ0) h).symm
end Sendov
