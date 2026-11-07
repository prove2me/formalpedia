-- Prove2me | solution 2 for QEC.Coding.f256RMFEpsi_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:30.605844+00:00
-- url     : https://prove2.me/submissions/22282cd3-f1bb-4d02-88f2-719a2adce66d

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Theorems.Thm_QEC_Coding_f256RMFEpsi_phi

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Function.Surjective f256RMFEpsi := by
  intro bit
  exact ⟨f256RMFEphi bit, f256RMFEpsi_phi bit⟩
end QEC.Coding
