-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.colength_sq_blockVandermonde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:30:55.26922+00:00
-- url     : https://prove2.me/submissions/6408cdfa-54e5-4514-9071-8d380716704f

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Theorems.Thm_ReciprocityTheory_PGsh_Up_sumLat_det
import Theorems.Thm_ReciprocityTheory_PGsh_Up_sumLat_pts
import Theorems.Thm_ReciprocityTheory_PGsh_Up_v_det_freeMat_sq
import Theorems.Thm_ReciprocityTheory_PGsh_colen_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n : ℕ} (a : Fin n → C) (s : ℕ) (F S : Lat v (Fin n × Fin s))
    (hF : F.B = freeMat a s) (hS : S.pts = sumPts (fun _ => Lat.std v (Fin s))) :
    colen F S ^ 2 = v (discr a) ^ s := by
  rw [colen_congr (L₂' := F) (L₂ := sumLat fun _ => Lat.std v (Fin s)) rfl
    (hS.trans (sumLat_pts _).symm)]
  rw [colen, sumLat_det]
  simp only [Lat.std, Matrix.det_one, map_one, Finset.prod_const_one, div_one, hF]
  exact v_det_freeMat_sq a s
end ReciprocityTheory.PGsh.Up
