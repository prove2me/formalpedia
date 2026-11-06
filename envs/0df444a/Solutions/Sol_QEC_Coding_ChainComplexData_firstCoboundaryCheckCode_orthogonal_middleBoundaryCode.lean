-- Prove2me | solution 1 for QEC.Coding.ChainComplexData.firstCoboundaryCheckCode_orthogonal_middleBoundaryCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:31.421096+00:00
-- url     : https://prove2.me/submissions/ea056da3-bdad-4029-a33e-c5d55bee92c3

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_LinearCode_symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.ChainComplexData
variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]
namespace QEC.Coding.ChainComplexData
theorem _root_.solution {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    ∀ x : Word F ι, x ∈ K.firstCoboundaryCheckCode.carrier →
      ∀ z : Word F ι, z ∈ K.middleBoundaryCode.carrier →
        symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
          ({ xPart := 0, zPart := z } : SymplecticVector F ι) = 0 := by
  intro x hx z hz
  exact LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
    K.firstCoboundaryCheckCode hx
    (K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual hz)
end QEC.Coding.ChainComplexData
