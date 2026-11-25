-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.lenId_of_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:08.222129+00:00
-- url     : https://prove2.me/submissions/3cdfe457-d4d6-4449-8788-449efa72d7c5

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_hasLen_coker_det__d6b912bda411
import Theorems.Thm_ReciprocityTheory_PGsh_Up_lenId_of


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
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hB : LenIdBStatement) : LenIdStatement :=
  lenId_of (fun C _ v R _ _ hv => hasLen_coker_det' v R hv) hB
end ReciprocityTheory.PGsh.Up
