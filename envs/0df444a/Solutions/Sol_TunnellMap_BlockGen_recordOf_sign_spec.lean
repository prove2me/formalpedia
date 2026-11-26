-- Prove2me | solution 1 for TunnellMap.BlockGen.recordOf_sign_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:24:11.244705+00:00
-- url     : https://prove2.me/submissions/96f66260-0528-4162-84d7-4498ed0abd11

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Theorems.Thm_TunnellMap_canonicalTargetLift_spec


set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) :
    targetValue s F i = vsmul (recordOf s F i).sign (recordOf s F i).target :=
  canonicalTargetLift_spec _
end TunnellMap.BlockGen
