-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_6_lambda_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:43.764355+00:00
-- url     : https://prove2.me/submissions/25f4c054-c897-42bb-9837-e564124573bd

import Mathlib.Computability.RE
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_1


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (t : Term) :
    IsScottContinuous (fun v => interp t (envSet (fun _ => botElem) 0 v)) :=
  theorem_2_1 t (fun _ => botElem) 0
end Scott1976.DataTypesAsLattices
