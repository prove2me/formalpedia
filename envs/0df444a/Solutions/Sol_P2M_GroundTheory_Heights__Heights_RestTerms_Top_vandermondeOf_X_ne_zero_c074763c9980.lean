-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_X_ne_zero_c074763c9980
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:53.514366+00:00
-- url     : https://prove2.me/submissions/a632ccec-21e6-4cc5-ad77-759d02904e58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (f N : ℕ) (τ : Fin f) :
    vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N)) ≠ 0 := by
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := (ne_of_lt (Finset.mem_Ioi.mp hj))
  refine sub_ne_zero.mpr fun h => hij ?_
  have := X_injective (R := ℚ) h
  simpa using this
end GroundTheory.Heights₂.Heights.RestTerms.Top
