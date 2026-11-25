-- Prove2me | solution 1 for OptimalAffinity.oa2x2_oneWayFluxes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:26.959801+00:00
-- url     : https://prove2.me/submissions/2dfca00c-8407-489b-9330-fcba288ad849

module
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Definitions.Def_proofs_OptimalAffinity_Steady

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution (x y : ℝ) :
    forwardFlux oa2x2 0 x y = 3 * x ∧
    reverseFlux oa2x2 0 x y = 2 * y ∧
    forwardFlux oa2x2 1 x y = 7 * y ^ 2 ∧
    reverseFlux oa2x2 1 x y = 6 * x ^ 2 * y := by
  norm_num [forwardFlux, reverseFlux, oa2x2]
end OptimalAffinity
