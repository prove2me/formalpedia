-- Prove2me | solution 1 for TeleportGates.Ck.teleport_one_qubit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:30:37.861567+00:00
-- url     : https://prove2.me/submissions/b0560796-f15f-4fb4-bc06-a8092eb0e89a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_TeleportGates_Ck_bell1
import Definitions.Def_TeleportGates_Ck_epr1
import Definitions.Def_TeleportGates_Ck_teleportOutput

open QAlgorithms

open TeleportGates.Ck QAlgorithms in
theorem solution (x z : Bool) (α : EuclideanSpace ℂ Bool) :
    teleportOutput (bell1 x z) α epr1 =
        (1 / 2 : ℂ) • act ((if x then pauliX else 1) * (if z then pauliZ else 1)) α ∧
      ‖teleportOutput (bell1 x z) α epr1‖ ^ 2 = ‖α‖ ^ 2 / 4 := by
  have hss : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Complex.ofReal_ofNat,
      one_div]
  have hs : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have h1 : teleportOutput (bell1 x z) α epr1 =
      (1 / 2 : ℂ) • act ((if x then pauliX else 1) * (if z then pauliZ else 1)) α := by
    rw [← hss]
    unfold teleportOutput bell1 epr1
    have hs' : (starRingEnd ℂ) ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := hs
    apply PiLp.ext
    intro c
    cases x <;> cases z <;> cases c <;>
      simp [act, pauliX, pauliZ, Matrix.mulVec, dotProduct, Fintype.sum_bool, Matrix.mul_apply,
        Matrix.one_apply, Matrix.diagonal_apply, hs, hs'] <;> ring
  refine ⟨h1, ?_⟩
  rw [h1, norm_smul, mul_pow]
  have hM : ‖act ((if x then pauliX else 1) * (if z then pauliZ else 1)) α‖ ^ 2 = ‖α‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_bool, Fintype.sum_bool]
    cases x <;> cases z <;>
      simp [act, pauliX, pauliZ, Matrix.mulVec, dotProduct, Fintype.sum_bool, Matrix.mul_apply,
        Matrix.one_apply] <;> ring
  rw [hM]
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  ring
