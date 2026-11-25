-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rootPoly_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:34.036524+00:00
-- url     : https://prove2.me/submissions/d97a735c-0563-4a1e-8096-1537a78a006d

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
theorem _root_.solution {x : K} (hx : x ∈ xs) :
    rootPoly xs = (X - C x) * rootPoly (xs.erase x) := by
  unfold rootPoly
  exact (Finset.mul_prod_erase xs (fun y => (X - C y : K[X])) hx).symm
end ReciprocityTheory.ChartRestriction.L1
