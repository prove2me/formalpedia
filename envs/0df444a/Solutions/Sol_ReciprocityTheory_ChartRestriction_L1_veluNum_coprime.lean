-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.veluNum_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:28:03.774778+00:00
-- url     : https://prove2.me/submissions/6dc98980-1932-41f9-80e3-dc35a322d667

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_eval_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_veluNum_eval_mem

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
theorem _root_.solution (h : ∀ x ∈ xs, fW g2 g3 x ≠ 0) :
    IsCoprime (veluNum g2 g3 xs) (rootPoly xs ^ 2) := by
  refine IsCoprime.pow_right ?_
  unfold rootPoly
  refine IsCoprime.prod_right (fun x hx => ?_)
  refine IsCoprime.symm ?_
  rw [(irreducible_X_sub_C x).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def,
    veluNum_eval_mem g2 g3 xs hx]
  exact mul_ne_zero (h x hx) (pow_ne_zero 2 (rootPoly_eval_ne _ (Finset.notMem_erase x xs)))
end ReciprocityTheory.ChartRestriction.L1
