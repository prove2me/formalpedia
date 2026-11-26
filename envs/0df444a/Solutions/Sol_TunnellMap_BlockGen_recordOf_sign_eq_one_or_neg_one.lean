-- Prove2me | solution 1 for TunnellMap.BlockGen.recordOf_sign_eq_one_or_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:48:26.744803+00:00
-- url     : https://prove2.me/submissions/b88c3748-a367-4a8a-baa7-348401149b43

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Theorems.Thm_TunnellMap_targetLiftSign_mem


set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex) :
    (recordOf s F i).sign = 1 ∨ (recordOf s F i).sign = -1 :=
  targetLiftSign_mem _
end TunnellMap.BlockGen
