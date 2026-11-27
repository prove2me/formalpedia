-- Prove2me | solution 1 for ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:38.382914+00:00
-- url     : https://prove2.me/submissions/f43d263f-1508-41e8-b8a4-654557922613

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.AB ReciprocityTheory.CA.AB.RegA
open ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing
open IsLocalRing
universe u
namespace ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing
theorem _root_.solution {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  haveI := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).2
end ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing
