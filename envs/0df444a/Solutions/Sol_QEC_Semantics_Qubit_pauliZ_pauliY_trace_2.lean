-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliZ_pauliY_trace
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:52:38.293784+00:00
-- url     : https://prove2.me/submissions/20f8e351-e9ce-402f-9720-0313f86840aa

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u

theorem solution :
    LinearMap.trace Complex QubitSpace (pauliZ * pauliY) = 0 := by
  have hanti : pauliZ * pauliY = -(pauliY * pauliZ) := by
    ext ψ b
    fin_cases b <;>
      simp [Module.End.mul_apply, pauliY_apply, pauliZ_apply, zPhase] <;> ring
  let T := LinearMap.trace Complex QubitSpace (pauliZ * pauliY)
  suffices hT : T = 0 by simpa [T] using hT
  have ht : T = -T := by
    dsimp [T]
    calc
      LinearMap.trace Complex QubitSpace (pauliZ * pauliY)
          = LinearMap.trace Complex QubitSpace (-(pauliY * pauliZ)) := by rw [hanti]
      _ = -LinearMap.trace Complex QubitSpace (pauliY * pauliZ) := by simp
      _ = -LinearMap.trace Complex QubitSpace (pauliZ * pauliY) := by
            rw [LinearMap.trace_mul_comm Complex pauliY pauliZ]
  have hsum : T + T = 0 := eq_neg_iff_add_eq_zero.mp ht
  have htwo : (2 : Complex) * T = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
