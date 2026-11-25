-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.freeMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:45:32.165216+00:00
-- url     : https://prove2.me/submissions/1caf7743-64b2-4a45-8d4b-2428a115fe80

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
theorem _root_.solution {n : ℕ} (a : Fin n → C) (s : ℕ) :
    freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [freeMat, Matrix.of_apply, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]
end ReciprocityTheory.PGsh.Up
