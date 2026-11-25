-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.det_freeMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:56:36.015716+00:00
-- url     : https://prove2.me/submissions/1f6bdaac-23bc-4b5f-8504-614dab9e0dae

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Theorems.Thm_ReciprocityTheory_PGsh_Up_freeMat_eq

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
theorem _root_.solution {n : ℕ} (a : Fin n → C) (s : ℕ) :
    (freeMat a s).det = (Matrix.vandermonde a).det ^ s := by
  rw [freeMat_eq, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end ReciprocityTheory.PGsh.Up
