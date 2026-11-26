-- Prove2me | solution 1 for TunnellMap.reconstructedTarget_same_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:47.181606+00:00
-- url     : https://prove2.me/submissions/6f1b284c-962c-4159-a83f-1038f2ca106b

import Definitions.Def_TunnellMap_GeneratorRecovery
import Definitions.Def_TunnellMap_GeneratorSoundness
import Theorems.Thm_TunnellMap_qForm_reconstructedTarget

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {E d : Triple} {A q : ℤ}
    (hA : qForm d = A) (hB : qBilinear E d = q * A) :
    qForm (reconstructedTarget E q d) = qForm E := by
  rw [qForm_reconstructedTarget, hA, hB]
  ring
end TunnellMap
