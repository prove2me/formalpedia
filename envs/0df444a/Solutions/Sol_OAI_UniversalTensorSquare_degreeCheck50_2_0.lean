-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck50_2_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:29:27.424192+00:00
-- url     : https://prove2.me/submissions/16ff0c94-3cac-4b55-a1c7-102c3300c9f2

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck50_2_0_oai :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 1 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck50_2_0_oai := @OAI.UniversalTensorSquare.degreeCheck50_2_0_oai
