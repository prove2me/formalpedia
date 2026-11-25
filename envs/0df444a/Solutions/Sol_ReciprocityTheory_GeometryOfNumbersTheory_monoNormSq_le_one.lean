-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:41.582489+00:00
-- url     : https://prove2.me/submissions/c94e7c68-52c3-4b7e-83c5-da4581fd233a

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_prod_fact_mul_fact_le

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
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) : monoNormSq a ≤ 1 := by
  unfold monoNormSq
  have hF : (0 : ℝ) < (((∑ i, a i) + D).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hle : ((∏ i, (a i).factorial : ℕ) : ℝ) * (D.factorial : ℝ) ≤ (((∑ i, a i) + D).factorial : ℝ) := by
    exact_mod_cast chiPAux_prod_fact_mul_fact_le a
  first
    | exact (div_le_one hF).mpr hle
    | exact (div_le_one₀ hF).mpr hle
    | exact div_le_one_of_le₀ hle hF.le
end ReciprocityTheory.GeometryOfNumbersTheory
