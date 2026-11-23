-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:38.426366+00:00
-- url     : https://prove2.me/submissions/4412185a-6e01-4b28-adba-aab08816037f

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
theorem _root_.solution {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : bd1 P 0 0 = 1 := rfl
end ReciprocityTheory.PGsh.Up.Smith
