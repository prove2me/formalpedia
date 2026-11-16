-- Prove2me | solution 1 for OAI.UniversalTensorSquare.eightCertificate8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:47:37.179194+00:00
-- url     : https://prove2.me/submissions/72e8d8c0-ccd3-44a0-9d93-f1016a13977e

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

lemma eightCertificate8_oai : contractionInteger [4,2,1,1] [4,2,1,1] [3,2,2,1]
    (Equiv.refl (Fin 8)) eightPlaceB8 eightPlaceT8 eightFlag8 = -3 := by
  unfold eightFlag8
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.eightCertificate8_oai := @OAI.UniversalTensorSquare.eightCertificate8_oai
