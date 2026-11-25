-- Prove2me | solution 1 for OptimalAffinity.oa2x2_ySteady_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:35.885014+00:00
-- url     : https://prove2.me/submissions/8e88ec11-b17a-4fa9-9e93-cdccbf32d260

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
    YSteady oa2x2 x y ↔ 3 * x - 2 * y = 7 * y ^ 2 - 6 * x ^ 2 * y := by
  simp only [YSteady]
  rw [oa2x2_netFluxes x y |>.1, oa2x2_netFluxes x y |>.2]
  norm_num [netY, oa2x2]
  constructor <;> intro h <;> linarith
end OptimalAffinity
