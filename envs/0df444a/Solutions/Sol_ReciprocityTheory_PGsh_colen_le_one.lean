-- Prove2me | solution 1 for ReciprocityTheory.PGsh.colen_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:23.262652+00:00
-- url     : https://prove2.me/submissions/99560dc2-e96d-4bed-946c-1ebe000bc9be

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_det_le_one
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_pts_subset_iff
import Theorems.Thm_ReciprocityTheory_PGsh_colen_eq_v_det

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
theorem _root_.solution {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) : colen L' L ≤ 1 := by
  rw [colen_eq_v_det]
  exact ((ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h).det_le_one
end ReciprocityTheory.PGsh
