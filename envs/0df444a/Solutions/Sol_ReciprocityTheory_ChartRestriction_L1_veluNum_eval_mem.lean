-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.veluNum_eval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:00.797335+00:00
-- url     : https://prove2.me/submissions/4d6da8b1-7a37-4d20-99a4-4f8d0deeb793

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_eval_mem
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_veluNum_eval__c23d48b99d50

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
theorem _root_.solution {x : K} (hx : x ∈ xs) :
    (veluNum g2 g3 xs).eval x = fW g2 g3 x * (rootPoly (xs.erase x)).eval x ^ 2 := by
  rw [veluNum_eval', rootPoly_eval_mem xs hx, Finset.sum_eq_single_of_mem x hx]
  · simp
  · intro y _ hy
    rw [rootPoly_eval_mem (xs.erase y) (Finset.mem_erase.2 ⟨hy.symm, hx⟩)]
    simp
end ReciprocityTheory.ChartRestriction.L1
