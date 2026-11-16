-- Prove2me | solution 1 for OAI.UniversalTensorSquare.partitionLists_five
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:33:24.918191+00:00
-- url     : https://prove2.me/submissions/1e956473-7ef3-4b20-98e3-a8fe1156b106

import Mathlib
import Definitions.Def_OAIQ259US001

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

noncomputable section

lemma partitionLists_five_oai : partitionLists 5 5 5 =
    {[5],[4,1],[3,2],[3,1,1],[2,2,1],[2,1,1,1],[1,1,1,1,1]} := by decide

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.partitionLists_five_oai := @OAI.UniversalTensorSquare.partitionLists_five_oai
