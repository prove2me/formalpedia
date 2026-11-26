-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_6_combinatory_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:45.878207+00:00
-- url     : https://prove2.me/submissions/dd4e93b7-0e8b-4ed9-9a95-266fc32c834a

import Mathlib.Computability.RE
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Computability

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution : IsLambdaDefinable zeroC :=
  ⟨Term.zero, rfl⟩
end Scott1976.DataTypesAsLattices
