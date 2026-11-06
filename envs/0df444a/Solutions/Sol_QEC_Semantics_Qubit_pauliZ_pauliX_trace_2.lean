-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliZ_pauliX_trace
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:51:46.693193+00:00
-- url     : https://prove2.me/submissions/a675de87-47ad-4932-9d65-d89b4334d50a

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
    LinearMap.trace Complex QubitSpace (pauliZ * pauliX) = 0 := by
  have hanti : pauliZ * pauliX = -(pauliX * pauliZ) := by
    ext ψ b
    fin_cases b <;>
      simp [Module.End.mul_apply, pauliX_apply, pauliZ_apply, zPhase] <;> ring
  let T := LinearMap.trace Complex QubitSpace (pauliZ * pauliX)
  suffices hT : T = 0 by simpa [T] using hT
  have ht : T = -T := by
    dsimp [T]
    calc
      LinearMap.trace Complex QubitSpace (pauliZ * pauliX)
          = LinearMap.trace Complex QubitSpace (-(pauliX * pauliZ)) := by rw [hanti]
      _ = -LinearMap.trace Complex QubitSpace (pauliX * pauliZ) := by simp
      _ = -LinearMap.trace Complex QubitSpace (pauliZ * pauliX) := by
            rw [LinearMap.trace_mul_comm Complex pauliX pauliZ]
  have hsum : T + T = 0 := eq_neg_iff_add_eq_zero.mp ht
  have htwo : (2 : Complex) * T = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
