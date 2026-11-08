-- Prove2me | solution 1 for TeleportGates.Ck.teleportOutput_gateResource
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:58:55.707207+00:00
-- url     : https://prove2.me/submissions/d6ca4c82-4a07-439e-a6a6-1a59ed895662

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_TeleportGates_Ck_gateResource
import Definitions.Def_TeleportGates_Ck_teleportOutput

open QAlgorithms

open TeleportGates.Ck QAlgorithms in
theorem solution {ι : Type*} [Fintype ι] (β : EuclideanSpace ℂ (ι × ι))
    (ψ : EuclideanSpace ℂ ι) (Φ : EuclideanSpace ℂ (ι × ι)) (U : Matrix ι ι ℂ) :
    teleportOutput β ψ (gateResource U Φ) = act U (teleportOutput β ψ Φ) := by
  apply PiLp.ext
  intro c
  simp only [teleportOutput, gateResource, act, PiLp.toLp_apply, WithLp.ofLp_toLp,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c' _
  apply Finset.sum_congr rfl
  intro b _
  ring
