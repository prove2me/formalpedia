-- Prove2me | solution 1 for QEC.Coding.LinearCode.dual_dual_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:07:02.285213+00:00
-- url     : https://prove2.me/submissions/5173be13-8096-411f-bc18-90a12d6b2f9c

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality
import Theorems.Thm_QEC_Coding_LinearCode_eq_of_carrier_eq
import Theorems.Thm_QEC_Coding_LinearCode_dual_dual_carrier_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C : LinearCode F ι) : C.dual.dual = C :=
  eq_of_carrier_eq (dual_dual_carrier_eq C)
end QEC.Coding.LinearCode
