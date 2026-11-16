-- Prove2me | solution 1 for OAI.UniversalTensorSquare.eightCertificate0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:47:31.462707+00:00
-- url     : https://prove2.me/submissions/801f5721-3648-4e6f-b809-331da03c10d4

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_Saxl_Columns_contractionInteger_compact

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeEight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Eight. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma eightCertificate0_oai : contractionInteger [4,2,1,1] [4,2,1,1] [1,1,1,1,1,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB0 eightPlaceT0 eightFlag0 = 6 := by
  unfold eightFlag0
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.eightCertificate0_oai := @OAI.UniversalTensorSquare.eightCertificate0_oai
