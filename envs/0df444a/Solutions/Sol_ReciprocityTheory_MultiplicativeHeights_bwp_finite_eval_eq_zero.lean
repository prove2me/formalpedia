-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_finite_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:22.961272+00:00
-- url     : https://prove2.me/submissions/efab2e34-c338-4bc0-bcba-28feef4ebf1e

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {P : ℂ[X]} (hP : P ≠ 0) : {t : ℂ | P.eval t = 0}.Finite := Polynomial.finite_setOf_isRoot hP
end ReciprocityTheory.MultiplicativeHeights
