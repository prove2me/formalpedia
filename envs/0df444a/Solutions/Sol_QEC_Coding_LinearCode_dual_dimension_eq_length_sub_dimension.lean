-- Prove2me | solution 1 for QEC.Coding.LinearCode.dual_dimension_eq_length_sub_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:17:16.204748+00:00
-- url     : https://prove2.me/submissions/b7e7b81e-5f07-40f8-878e-bbdc8e64d7e9

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C : LinearCode F ι) :
    Dimension C.dual = Length F ι - Dimension C := by
  have hB : (LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))).Nondegenerate :=
    (wordPairing_nondegenerate (F := F) (ι := ι)).flip
  calc
    Dimension C.dual = Module.finrank F C.dual.carrier := rfl
    _ = Module.finrank F
          ((LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))).orthogonal
            C.carrier) := by
        rw [LinearCode.dual_carrier]
    _ = Module.finrank F (Word F ι) - Module.finrank F C.carrier := by
        exact LinearMap.BilinForm.finrank_orthogonal hB C.carrier
    _ = Length F ι - Dimension C := by
        rw [finrank_word_eq_length, Dimension_eq_finrank_carrier]
end QEC.Coding.LinearCode
