-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_poly_eq_of_eval_eq_off
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:23.73892+00:00
-- url     : https://prove2.me/submissions/c29ad7ce-d86f-4149-94cb-7bb18d303b52

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
theorem _root_.solution (P Q : ℂ[X]) (E : Set ℂ) (hE : E.Finite)
    (h : ∀ t ∉ E, P.eval t = Q.eval t) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (fun t ht => h t ht) hE.infinite_compl
end ReciprocityTheory.MultiplicativeHeights
