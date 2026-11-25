-- Prove2me | solution 1 for PI.WeylProdWork.denom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:13:21.821413+00:00
-- url     : https://prove2.me/submissions/a021be7c-06de-4dd8-ada7-216bb02d5789

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
theorem _root_.solution (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  have h1 : ∀ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) = (((n - 1 - i).factorial : ℕ) : ℝ) := by
    intro i hi
    rw [mem_range] at hi
    rw [Finset.prod_Ico_eq_prod_range]
    have e : n - (i + 1) = n - 1 - i := by omega
    rw [e, ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    exact Finset.prod_congr rfl (fun t _ => by ring)
  rw [Finset.prod_congr rfl h1]
  exact Finset.prod_range_reflect (fun i => ((i.factorial : ℕ) : ℝ)) n
end PI.WeylProdWork
