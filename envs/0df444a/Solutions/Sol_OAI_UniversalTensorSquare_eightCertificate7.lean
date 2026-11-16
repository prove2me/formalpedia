-- Prove2me | solution 1 for OAI.UniversalTensorSquare.eightCertificate7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:46:27.229401+00:00
-- url     : https://prove2.me/submissions/447ff5be-51a1-4d4a-9c99-09e048eb4c9b

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

lemma eightCertificate7_oai : contractionInteger [4,2,1,1] [4,2,1,1] [2,2,2,2]
    (Equiv.refl (Fin 8)) eightPlaceB7 eightPlaceT7 eightFlag7 = 2 := by
  unfold eightFlag7
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.eightCertificate7_oai := @OAI.UniversalTensorSquare.eightCertificate7_oai
