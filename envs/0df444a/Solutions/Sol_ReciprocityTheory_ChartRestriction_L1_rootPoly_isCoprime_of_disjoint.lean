-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rootPoly_isCoprime_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:05:44.751089+00:00
-- url     : https://prove2.me/submissions/b3bffabb-e5ec-4c43-ad98-09550f4f23b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedGcd

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
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {E : Type} [Field E] (xs ys : Finset E) (h : Disjoint xs ys) :
    IsCoprime (rootPoly xs) (rootPoly ys) := by
  unfold rootPoly
  refine IsCoprime.prod_left fun x hx => IsCoprime.prod_right fun y hy => ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  have hne : x ≠ y := fun e => Finset.disjoint_left.1 h hx (e ▸ hy)
  exact (sub_ne_zero.2 hne).isUnit
end ReciprocityTheory.ChartRestriction.L1
