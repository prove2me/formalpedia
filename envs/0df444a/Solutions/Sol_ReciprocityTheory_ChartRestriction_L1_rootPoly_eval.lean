-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rootPoly_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:09.622307+00:00
-- url     : https://prove2.me/submissions/05186075-395c-4859-b224-d391fa4ef27c

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
theorem _root_.solution (t : K) : (rootPoly xs).eval t = ∏ x ∈ xs, (t - x) := by
  unfold rootPoly
  rw [eval_prod]
  simp
end ReciprocityTheory.ChartRestriction.L1
