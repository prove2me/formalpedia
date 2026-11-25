-- Prove2me | solution 1 for OptimalAffinity.oa2x2_tightCoupling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:19.506216+00:00
-- url     : https://prove2.me/submissions/a76ec1b2-e7ac-418d-a792-27810cd248e9

module
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Theorems.Thm_OptimalAffinity_oa2x2_netFluxes
public import Theorems.Thm_OptimalAffinity_oa2x2_ySteady_iff

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution {x y : ℝ} (hsteady : YSteady oa2x2 x y) :
    netFlux oa2x2 0 x y = netFlux oa2x2 1 x y := by
  rw [oa2x2_netFluxes x y |>.1, oa2x2_netFluxes x y |>.2]
  exact (oa2x2_ySteady_iff x y).mp hsteady
end OptimalAffinity
