-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rootPoly_eval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:53.713663+00:00
-- url     : https://prove2.me/submissions/6d30118e-e0a1-44ec-b69c-75774c476ad7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {K : Type} [Field K] [CharZero K] [DecidableEq K] (g2 g3 : K) (xs : Finset K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {t : K} (ht : t ∈ xs) : (rootPoly xs).eval t = 0 := by
  rw [rootPoly_eval]
  exact Finset.prod_eq_zero ht (sub_self t)
end ReciprocityTheory.ChartRestriction.L1
