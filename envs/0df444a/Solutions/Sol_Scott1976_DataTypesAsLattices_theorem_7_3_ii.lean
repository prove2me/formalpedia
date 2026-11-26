-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_7_3_ii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:17.010441+00:00
-- url     : https://prove2.me/submissions/af2cef22-cc3c-4fa4-bb98-b5e1af31aefa

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (A B : RestrictedEquiv) {x x' : Pomega}
    (h : A.rel x x') :
    (arrowE B A).rel (funOf Kcomb x) (funOf Kcomb x') ∨
      A.rel x x' :=
  Or.inr h
end Scott1976.DataTypesAsLattices
