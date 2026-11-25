-- Prove2me | solution 1 for PI.WeylProdWork.row_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:15:38.233224+00:00
-- url     : https://prove2.me/submissions/01d22611-24b0-41a7-9c1b-05a4f5d7c96b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylProduct_WeylProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WeylProdWork
open Finset
namespace PI.WeylProdWork
theorem _root_.solution (x : ℕ → ℝ) (n i : ℕ) :
    ∏ j ∈ range n, wg x i j =
      (∏ j ∈ Ico (i + 1) n, (x i - x j)) / ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) := by
  rw [← Finset.prod_div_distrib]
  by_cases hin : i + 1 ≤ n
  · rw [← Finset.prod_range_mul_prod_Ico _ hin]
    have h1 : ∏ j ∈ range (i + 1), wg x i j = 1 := Finset.prod_eq_one (fun j hj => by
      rw [mem_range] at hj
      simp [wg, show ¬ i < j by omega])
    rw [h1, one_mul]
    exact Finset.prod_congr rfl (fun j hj => by
      rw [mem_Ico] at hj
      simp [wg, show i < j by omega])
  · push_neg at hin
    rw [Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty]
    exact Finset.prod_eq_one (fun j hj => by
      rw [mem_range] at hj
      simp [wg, show ¬ i < j by omega])
end PI.WeylProdWork
