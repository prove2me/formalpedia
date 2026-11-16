-- Prove2me | solution 1 for OAI.UniversalTensorSquare.eightCertificate10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:47:34.404945+00:00
-- url     : https://prove2.me/submissions/78ac5c6c-5d0e-4cdc-abec-767a400fa6c1

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_Saxl_Columns_contractionInteger_compact

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_EightSplitCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eight Split Certificate. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma eightCertificate10_oai : contractionInteger [4,2,1,1] [4,2,1,1] [4,2,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB10 eightPlaceT10 eightFlag10 = -4 := by
  unfold eightFlag10
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.eightCertificate10_oai := @OAI.UniversalTensorSquare.eightCertificate10_oai
