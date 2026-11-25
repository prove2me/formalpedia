-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.matEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:37:20.75581+00:00
-- url     : https://prove2.me/submissions/6354184b-f7a0-4d10-a67f-e8733a003b79

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply

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
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {d : ℕ} (P : Matrix (Fin d) (Fin d) R) (hP : IsUnit P.det) (x : Fin d → R) :
    matEquiv P hP x = P *ᵥ x := by
  show Matrix.toLin' P x = P *ᵥ x
  rw [Matrix.toLin'_apply]
end ReciprocityTheory.PGsh.Up
