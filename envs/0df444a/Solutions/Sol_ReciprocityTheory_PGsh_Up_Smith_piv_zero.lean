-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.piv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:19.115752+00:00
-- url     : https://prove2.me/submissions/e37dd6c2-14a9-460a-8006-d2fa068a03f2

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
theorem _root_.solution {N : ℕ} (i0 : Fin (N + 1)) : piv i0 0 = i0 := by
  simp [piv, finSuccEquiv_zero]
end ReciprocityTheory.PGsh.Up.Smith
