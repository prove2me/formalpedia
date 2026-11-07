-- Prove2me | solution 1 for QEC.Coding.LinearCode.dual_inf_carrier_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:07:03.259806+00:00
-- url     : https://prove2.me/submissions/e4bf82b4-9db9-486f-aae0-ae30773c19f5

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality
import Theorems.Thm_QEC_Coding_LinearCode_eq_of_carrier_eq
import Theorems.Thm_QEC_Coding_LinearCode_dual_dual_carrier_eq
import Theorems.Thm_QEC_Coding_LinearCode_dual_sup_carrier_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C D : LinearCode F ι) :
    ({ carrier := C.carrier ⊓ D.carrier } : LinearCode F ι).dual.carrier =
      C.dual.carrier ⊔ D.dual.carrier := by
  let S : LinearCode F ι := ⟨C.dual.carrier ⊔ D.dual.carrier⟩
  have hS : S.dual = ({ carrier := C.carrier ⊓ D.carrier } : LinearCode F ι) := by
    apply eq_of_carrier_eq
    change ({ carrier := C.dual.carrier ⊔ D.dual.carrier } : LinearCode F ι).dual.carrier = _
    rw [dual_sup_carrier_eq, dual_dual_carrier_eq, dual_dual_carrier_eq]
  rw [← hS, dual_dual_carrier_eq]
end QEC.Coding.LinearCode
