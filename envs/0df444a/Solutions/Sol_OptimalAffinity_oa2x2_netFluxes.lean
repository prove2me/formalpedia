-- Prove2me | solution 1 for OptimalAffinity.oa2x2_netFluxes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:56:13.961142+00:00
-- url     : https://prove2.me/submissions/81326f46-23cf-4570-8962-b4f07183e1cd

module
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Definitions.Def_proofs_OptimalAffinity_Steady

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution (x y : ℝ) :
    netFlux oa2x2 0 x y = 3 * x - 2 * y ∧
    netFlux oa2x2 1 x y = 7 * y ^ 2 - 6 * x ^ 2 * y := by
  norm_num [netFlux, forwardFlux, reverseFlux, oa2x2]
end OptimalAffinity
