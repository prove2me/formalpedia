-- Prove2me | solution 1 for ReciprocityTheory.CA.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:44.586254+00:00
-- url     : https://prove2.me/submissions/7cc60a84-2536-4be0-8981-0dbbfa88ca7e

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGensA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.RegA
open ReciprocityTheory.CA.RegA.IsRegularLocalRing
open IsLocalRing
universe u
namespace ReciprocityTheory.CA.RegA.IsRegularLocalRing
theorem _root_.solution {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).2
end ReciprocityTheory.CA.RegA.IsRegularLocalRing
