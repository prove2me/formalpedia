-- Prove2me | solution 2 for QEC.Coding.f256RMFEphi_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:26.27387+00:00
-- url     : https://prove2.me/submissions/c868a07c-2dde-4d05-9949-e344c95d3f8b

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Theorems.Thm_QEC_Coding_f256RMFEphi_apply

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Function.Injective f256RMFEphi := by
  intro x y hxy
  exact (algebraMap (ZMod 2) F256).injective (by
    simpa only [f256RMFEphi_apply] using hxy)
end QEC.Coding
