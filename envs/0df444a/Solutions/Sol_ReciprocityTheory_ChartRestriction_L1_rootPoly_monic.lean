-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rootPoly_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:03.788835+00:00
-- url     : https://prove2.me/submissions/562df4ac-ccf6-4244-8121-0a5f4e3b6a5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg

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
theorem _root_.solution : (rootPoly xs).Monic := by
  unfold rootPoly
  exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
end ReciprocityTheory.ChartRestriction.L1
