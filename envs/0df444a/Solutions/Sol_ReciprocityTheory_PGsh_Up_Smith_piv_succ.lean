-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.piv_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:16.512878+00:00
-- url     : https://prove2.me/submissions/2d6f1cdd-4610-48e1-89e5-a93d5c94d773

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution {N : ℕ} (i0 : Fin (N + 1)) (l : Fin N) : piv i0 l.succ = i0.succAbove l := by
  simp [piv, finSuccEquiv_succ]
end ReciprocityTheory.PGsh.Up.Smith
