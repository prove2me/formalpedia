-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.lenId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:10:19.927221+00:00
-- url     : https://prove2.me/submissions/5487d75b-33b6-4e30-b39f-c8891cd2fd36

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Theorems.Thm_ReciprocityTheory_PGsh_Up_dualLen
import Theorems.Thm_ReciprocityTheory_PGsh_Up_lenIdB_of
import Theorems.Thm_ReciprocityTheory_PGsh_Up_lenId_of_B


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
theorem _root_.solution : LenIdStatement := lenId_of_B (lenIdB_of dualLen)
end ReciprocityTheory.PGsh.Up
