-- Prove2me | solution 2 for QEC.Coding.f256RMFE_ternary_reverse_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:36.028254+00:00
-- url     : https://prove2.me/submissions/1c2916b1-23ee-4c41-92b8-a72b5dd6fbac

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Theorems.Thm_QEC_Coding_f256RMFEphi_apply
import Theorems.Thm_QEC_Coding_f256RMFEpsi_phi

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (x y z : ZMod 2) :
    f256RMFEpsi (f256RMFEphi x * f256RMFEphi y * f256RMFEphi z) = x * y * z := by
  calc
    f256RMFEpsi (f256RMFEphi x * f256RMFEphi y * f256RMFEphi z) =
        f256RMFEpsi (f256RMFEphi (x * y * z)) := by
          congr 1
          simp only [f256RMFEphi_apply]
          rw [← map_mul, ← map_mul]
    _ = x * y * z := f256RMFEpsi_phi (x * y * z)
end QEC.Coding
