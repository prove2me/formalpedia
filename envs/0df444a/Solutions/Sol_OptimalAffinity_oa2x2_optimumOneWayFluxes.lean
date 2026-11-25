-- Prove2me | solution 1 for OptimalAffinity.oa2x2_optimumOneWayFluxes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:14.926999+00:00
-- url     : https://prove2.me/submissions/e00c1217-032d-4abe-9d97-2626a9d7a932

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution :
    forwardFlux oa2x2 0 1 1 = 3 ∧ reverseFlux oa2x2 0 1 1 = 2 ∧
    forwardFlux oa2x2 1 1 1 = 7 ∧ reverseFlux oa2x2 1 1 1 = 6 := by
  norm_num [forwardFlux, reverseFlux, oa2x2]
end OptimalAffinity
