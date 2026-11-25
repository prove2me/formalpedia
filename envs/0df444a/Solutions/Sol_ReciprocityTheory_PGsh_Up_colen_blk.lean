-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.colen_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:50.240994+00:00
-- url     : https://prove2.me/submissions/9e496150-90fe-483d-b0cb-4934947054db

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_blkLat_det

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
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n s : ℕ} (L's Ls : Fin n → Lat v (Fin s)) :
    colen (blkLat L's) (blkLat Ls) = ∏ τ, colen (L's τ) (Ls τ) := by
  simp only [ReciprocityTheory.PGsh.colen, blkLat_det, map_prod]
  rw [Finset.prod_div_distrib]
end ReciprocityTheory.PGsh.Up
