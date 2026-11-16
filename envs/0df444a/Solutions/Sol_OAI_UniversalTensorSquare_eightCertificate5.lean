-- Prove2me | solution 1 for OAI.UniversalTensorSquare.eightCertificate5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:46:24.473468+00:00
-- url     : https://prove2.me/submissions/c534035a-8430-4e34-bd1d-28ee64e683b2

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

lemma eightCertificate5_oai : contractionInteger [4,2,1,1] [4,2,1,1] [3,2,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB5 eightPlaceT5 eightFlag5 = 2 := by
  unfold eightFlag5
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.eightCertificate5_oai := @OAI.UniversalTensorSquare.eightCertificate5_oai
