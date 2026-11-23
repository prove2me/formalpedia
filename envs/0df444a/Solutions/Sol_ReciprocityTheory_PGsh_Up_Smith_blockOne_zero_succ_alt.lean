-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:37.862898+00:00
-- url     : https://prove2.me/submissions/bda49964-71a3-4bc6-9c8f-97d00981ab2e

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
theorem _root_.solution {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (k : Fin M) :
    bd1 P 0 k.succ = 0 := rfl
end ReciprocityTheory.PGsh.Up.Smith
