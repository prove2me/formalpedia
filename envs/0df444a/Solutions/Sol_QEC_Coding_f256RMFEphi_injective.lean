-- Prove2me | solution 1 for QEC.Coding.f256RMFEphi_injective
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:50:16.135733+00:00
-- url     : https://prove2.me/submissions/39c982e2-3890-4cc4-8f1f-d2d92b528946

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
open QEC QEC.Coding
private theorem f256RMFEphi_apply (bit : ZMod 2) :
    f256RMFEphi bit = algebraMap (ZMod 2) F256 bit := by
  rw [f256RMFEphi, Algebra.linearMap_apply]
theorem solution : Function.Injective f256RMFEphi := by
  intro x y hxy
  exact (algebraMap (ZMod 2) F256).injective (by
    simpa only [f256RMFEphi_apply] using hxy)
