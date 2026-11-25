-- Prove2me | solution 1 for OptimalAffinity.oa2x2_current_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:37.683849+00:00
-- url     : https://prove2.me/submissions/7bb8c38c-81fd-4bfc-b483-4bb3d365bda9

module
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Theorems.Thm_OptimalAffinity_oa2x2_netFluxes

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution (x y : ℝ) :
    productionCurrent oa2x2 x y = 3 * x - 2 * y := by
  exact oa2x2_netFluxes x y |>.1
end OptimalAffinity
