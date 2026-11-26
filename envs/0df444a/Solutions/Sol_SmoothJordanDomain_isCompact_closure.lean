-- Prove2me | solution 1 for SmoothJordanDomain.isCompact_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:04.577813+00:00
-- url     : https://prove2.me/submissions/b06c5637-58bc-4313-8857-438f663b0f63

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier

set_option autoImplicit false
open Complex Metric Set
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    IsCompact (closure Omega.carrier) :=
  Omega.isBounded_carrier.isCompact_closure
end SmoothJordanDomain
