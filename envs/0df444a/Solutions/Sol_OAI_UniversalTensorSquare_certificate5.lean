-- Prove2me | solution 1 for OAI.UniversalTensorSquare.certificate5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:36:44.000801+00:00
-- url     : https://prove2.me/submissions/a3374a06-70b6-4c50-ad48-7bd750bd3e3d

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeFive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Five. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma certificate5_oai : contractionInteger [3,1,1] [3,1,1] [5]
    (Equiv.refl (Fin 5)) hookPlacement (Equiv.refl (Fin 5)) flag5 = 20 := by decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.certificate5_oai := @OAI.UniversalTensorSquare.certificate5_oai
