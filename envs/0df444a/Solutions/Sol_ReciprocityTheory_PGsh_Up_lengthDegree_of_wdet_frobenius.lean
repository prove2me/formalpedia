-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.lengthDegree_of_wdet_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:30.603616+00:00
-- url     : https://prove2.me/submissions/c6dcfe71-d623-4a55-af90-f5c22972268f

import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfWdetFrobenius
import Theorems.Thm_ReciprocityTheory_PGsh_Up_cokernelLowerBound_of
import Theorems.Thm_ReciprocityTheory_PGsh_Up_idemGen
import Theorems.Thm_ReciprocityTheory_PGsh_Up_killedGen
import Theorems.Thm_ReciprocityTheory_PGsh_Up_lenEx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hU6 : CokernelLengthComparisonStatement) (hU7 : UnramifiedCokernelLengthStatement) : CokernelLowerBoundStatement :=
  cokernelLowerBound_of hU6 hU7 lenEx killedGen idemGen
end ReciprocityTheory.PGsh.Up
