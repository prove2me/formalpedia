-- Prove2me | solution 1 for ReciprocityTheory.PGsh.colen_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:08.166163+00:00
-- url     : https://prove2.me/submissions/ac352828-73ad-40df-9a1d-e489fd203e3a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_isUnit_det
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_pts_subset_iff
import Theorems.Thm_ReciprocityTheory_PGsh_colen_eq_v_det
import Theorems.Thm_ReciprocityTheory_PGsh_colen_congr
import Theorems.Thm_ReciprocityTheory_PGsh_colen_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (hZ : ColengthZeroStatement) {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) :
    colen L' L = 1 ↔ L'.pts = L.pts := by
  constructor
  · intro h1
    have hM := (ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h
    rw [colen_eq_v_det] at h1
    have hInv := hZ K v ι _ hM h1
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (ReciprocityTheory.PGsh.Lat.isUnit_det L)] at hInv
    exact Set.Subset.antisymm h ((ReciprocityTheory.PGsh.Lat.pts_subset_iff L L').mpr hInv)
  · intro he
    rw [colen_congr he rfl, colen_self]
end ReciprocityTheory.PGsh
