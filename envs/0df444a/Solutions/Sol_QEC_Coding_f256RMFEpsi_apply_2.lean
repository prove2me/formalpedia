-- Prove2me | solution 2 for QEC.Coding.f256RMFEpsi_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:48:48.925511+00:00
-- url     : https://prove2.me/submissions/e7bde9ac-92f9-44f1-8f21-962a13157c98

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (x : F256) :
    f256RMFEpsi x = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3 * x) := by
  rw [f256RMFEpsi, LinearMap.comp_apply, LinearMap.mulLeft_apply]
end QEC.Coding
