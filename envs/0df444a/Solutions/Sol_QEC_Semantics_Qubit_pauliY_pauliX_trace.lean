-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliY_pauliX_trace
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:40:27.102297+00:00
-- url     : https://prove2.me/submissions/20aee0b3-c6b6-4a85-8b94-908b5903f3f9

-- ID: 9333ca61-0a3f-4804-87db-0826ac7d567f | NAME: QEC.Semantics.Qubit.pauliY_pauliX_trace | 未本地编译验证
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
    LinearMap.trace Complex QubitSpace (pauliY * pauliX) = 0 := by
  have hanti : pauliY * pauliX = -(pauliX * pauliY) := by
    ext ψ b
    fin_cases b <;>
      simp [Module.End.mul_apply, pauliY_apply, pauliX_apply, flipBit] <;> ring
  let T := LinearMap.trace Complex QubitSpace (pauliY * pauliX)
  suffices hT : T = 0 by simpa [T] using hT
  have ht : T = -T := by
    dsimp [T]
    calc
      LinearMap.trace Complex QubitSpace (pauliY * pauliX)
          = LinearMap.trace Complex QubitSpace (-(pauliX * pauliY)) := by rw [hanti]
      _ = -LinearMap.trace Complex QubitSpace (pauliX * pauliY) := by simp
      _ = -LinearMap.trace Complex QubitSpace (pauliY * pauliX) := by
            rw [LinearMap.trace_mul_comm Complex pauliX pauliY]
  have hsum : T + T = 0 := eq_neg_iff_add_eq_zero.mp ht
  have htwo : (2 : Complex) * T = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
