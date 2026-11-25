-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sumLat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:34.204104+00:00
-- url     : https://prove2.me/submissions/09d36290-8853-4363-890e-e97d41a3272b

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
theorem _root_.solution {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (x y : Fin n × Fin s) :
    (sumLat Mτ).B x y = if x.1 = y.1 then (Mτ x.1).B x.2 y.2 else 0 := by
  simp only [sumLat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Matrix.blockDiagonal_apply]
end ReciprocityTheory.PGsh.Up
