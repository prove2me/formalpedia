-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:37.550836+00:00
-- url     : https://prove2.me/submissions/27b9caac-4bae-4d6a-947b-5f7a3a6200a0

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
theorem _root_.solution {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (l : Fin N) (k : Fin M) :
    bd1 P l.succ k.succ = P l k := rfl
end ReciprocityTheory.PGsh.Up.Smith
