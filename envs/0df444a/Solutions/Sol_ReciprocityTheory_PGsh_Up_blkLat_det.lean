-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.blkLat_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:40.823909+00:00
-- url     : https://prove2.me/submissions/7a0575ac-8951-4c97-aa91-df19a0ee5321

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd

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
theorem _root_.solution {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) :
    (blkLat Ls).B.det = ∏ τ, (Ls τ).B.det := by
  have h : (blkLat Ls).B =
      (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext x y
    simp [blkLat, Matrix.blockDiagonal_apply, eq_comm]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
end ReciprocityTheory.PGsh.Up
