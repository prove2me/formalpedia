-- Prove2me | solution 2 for QEC.Coding.f256RMFEpsi_phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:50:45.967666+00:00
-- url     : https://prove2.me/submissions/7c29cd72-1f20-4c02-a68c-47177277fc1d

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Theorems.Thm_QEC_Coding_f256RMFEphi_apply
import Theorems.Thm_QEC_Coding_f256RMFEpsi_apply
import Theorems.Thm_QEC_Coding_f256TraceAlphaCubed

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (bit : ZMod 2) :
    f256RMFEpsi (f256RMFEphi bit) = bit := by
  calc
    f256RMFEpsi (f256RMFEphi bit) =
        bit * Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) := by
          rw [f256RMFEpsi_apply, f256RMFEphi_apply]
          simpa [Algebra.smul_def, mul_comm] using
            (Algebra.trace (ZMod 2) F256).map_smul bit (f256Alpha ^ 3)
    _ = bit := by rw [f256TraceAlphaCubed, mul_one]
end QEC.Coding
