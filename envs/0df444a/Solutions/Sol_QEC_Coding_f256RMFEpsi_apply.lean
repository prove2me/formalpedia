-- Prove2me | solution 1 for QEC.Coding.f256RMFEpsi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:47:52.624311+00:00
-- url     : https://prove2.me/submissions/af3972f7-c80f-4196-a427-3fc5db6d7026

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem solution (x : F256) :
    f256RMFEpsi x = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3 * x) := by
  rw [f256RMFEpsi, LinearMap.comp_apply, LinearMap.mulLeft_apply]
