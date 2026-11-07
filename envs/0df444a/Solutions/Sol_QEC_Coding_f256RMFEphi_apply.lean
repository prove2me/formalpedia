-- Prove2me | solution 1 for QEC.Coding.f256RMFEphi_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:27.738481+00:00
-- url     : https://prove2.me/submissions/300af861-770e-44d1-ab88-6abc4c12706c

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (bit : ZMod 2) :
    f256RMFEphi bit = algebraMap (ZMod 2) F256 bit := by
  rw [f256RMFEphi, Algebra.linearMap_apply]
end QEC.Coding
