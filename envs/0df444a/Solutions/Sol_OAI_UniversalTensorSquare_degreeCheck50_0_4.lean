-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck50_0_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:29:19.480001+00:00
-- url     : https://prove2.me/submissions/88d8a8c6-a6b1-4fac-95d8-7184c14912a6

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

lemma degreeCheck50_0_4_oai :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 1 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck50_0_4_oai := @OAI.UniversalTensorSquare.degreeCheck50_0_4_oai
