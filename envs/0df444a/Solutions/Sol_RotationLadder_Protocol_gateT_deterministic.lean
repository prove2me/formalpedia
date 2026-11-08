-- Prove2me | solution 1 for RotationLadder.Protocol.gateT_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:09:42.404298+00:00
-- url     : https://prove2.me/submissions/c0a96010-4bc9-439a-94aa-5a6edd74dee6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_RotationLadder_Protocol_zRot

open RotationLadder.Protocol in
theorem solution :
    QAlgorithms.phaseS * RotationLadder.Protocol.zRot (-(Real.pi / 4)) = QAlgorithms.gateT ∧
      RotationLadder.Protocol.zRot (Real.pi / 4) = QAlgorithms.gateT ∧
        RotationLadder.Protocol.zRot (Real.pi / 2) = QAlgorithms.phaseS := by
  have hI : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring]
    exact Complex.exp_pi_div_two_mul_I
  refine ⟨?_, ?_, ?_⟩
  · unfold QAlgorithms.phaseS RotationLadder.Protocol.zRot QAlgorithms.gateT
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    cases a
    · simp
    · rw [if_pos rfl, if_pos rfl, if_pos rfl]
      nth_rewrite 1 [← hI]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
  · unfold RotationLadder.Protocol.zRot QAlgorithms.gateT
    congr 1
    funext a
    cases a
    · rfl
    · rw [if_pos rfl, if_pos rfl]
      congr 1
      push_cast
      ring
  · unfold RotationLadder.Protocol.zRot QAlgorithms.phaseS
    congr 1
    funext a
    cases a
    · rfl
    · rw [if_pos rfl, if_pos rfl]
      exact hI
