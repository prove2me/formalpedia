-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sumLat_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:35.974722+00:00
-- url     : https://prove2.me/submissions/22fc0744-7eab-4961-890b-2f8806ce96cb

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde

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
theorem _root_.solution {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) :
    (sumLat Mτ).B.det = ∏ τ, (Mτ τ).B.det := by
  show (Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal fun τ => (Mτ τ).B)).det = _
  rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
end ReciprocityTheory.PGsh.Up
