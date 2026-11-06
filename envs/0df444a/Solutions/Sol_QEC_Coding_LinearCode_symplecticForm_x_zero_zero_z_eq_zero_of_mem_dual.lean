-- Prove2me | solution 1 for QEC.Coding.LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:19:06.366993+00:00
-- url     : https://prove2.me/submissions/4a6dcecd-3a37-4b6f-a4a8-bb6234d4d618

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C : LinearCode F ι)
    {x z : Word F ι} (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        ({ xPart := 0, zPart := z } : SymplecticVector F ι) = 0 := by
  rw [symplecticForm_x_zero_zero_z_eq_wordPairing]
  exact C.dual_orthogonal hx hz
end QEC.Coding.LinearCode
