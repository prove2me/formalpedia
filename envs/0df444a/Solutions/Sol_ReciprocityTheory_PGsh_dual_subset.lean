-- Prove2me | solution 1 for ReciprocityTheory.PGsh.dual_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:32.261706+00:00
-- url     : https://prove2.me/submissions/7090acf5-670d-48b2-85cc-2ad09bd192af

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_isUnit_det
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_pts_subset_iff

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
theorem _root_.solution {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) : L.dual.pts ⊆ L'.dual.pts := by
  have hM := (ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h
  rw [ReciprocityTheory.PGsh.Lat.pts_subset_iff]
  show IsIntegralMat v (((L'.Bᵀ)⁻¹)⁻¹ * (L.Bᵀ)⁻¹)
  rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact ReciprocityTheory.PGsh.Lat.isUnit_det L'),
    ← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul]
  intro i j
  exact hM j i
end ReciprocityTheory.PGsh
