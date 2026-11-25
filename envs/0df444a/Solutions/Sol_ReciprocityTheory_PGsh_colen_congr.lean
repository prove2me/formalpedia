-- Prove2me | solution 1 for ReciprocityTheory.PGsh.colen_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:42.503337+00:00
-- url     : https://prove2.me/submissions/2ae9dd7e-bc8b-4830-b8ec-54409871269e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_v_det_eq_of_pts_eq

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
theorem _root_.solution {L₁' L₂' L₁ L₂ : Lat v ι} (h' : L₁'.pts = L₂'.pts) (h : L₁.pts = L₂.pts) :
    colen L₁' L₁ = colen L₂' L₂ := by
  unfold colen
  rw [ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h', ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h]
end ReciprocityTheory.PGsh
