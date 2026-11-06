-- Prove2me | solution 1 for QEC.Coding.symplecticForm_x_zero_zero_z_eq_wordPairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:15:08.131856+00:00
-- url     : https://prove2.me/submissions/94e7fd10-28c7-4889-9872-6fb6ac98fb86

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
namespace QEC.Coding
theorem _root_.solution {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [Fintype ι] (x z : Word F ι) :
    symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        ({ xPart := 0, zPart := z } : SymplecticVector F ι) =
      wordPairing (F := F) (ι := ι) x z := by
  simp [symplecticForm, wordPairing_apply, dotProduct]
end QEC.Coding
