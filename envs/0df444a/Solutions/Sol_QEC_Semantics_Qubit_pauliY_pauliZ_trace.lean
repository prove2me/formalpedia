-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliY_pauliZ_trace
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:12:29.343825+00:00
-- url     : https://prove2.me/submissions/93b2d238-2009-451d-8fd2-b205087e45e3

-- ID: 65847502-ba45-4cda-b8b4-3a6421f73540 | NAME: QEC.Semantics.Qubit.pauliY_pauliZ_trace | 未本地编译验证
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
    LinearMap.trace Complex QubitSpace (pauliY * pauliZ) = 0 := by
  have hanti : pauliY * pauliZ = -(pauliZ * pauliY) := by
    ext ψ b
    fin_cases b <;>
      simp [Module.End.mul_apply, pauliY_apply, pauliZ_apply, zPhase] <;> ring
  let T := LinearMap.trace Complex QubitSpace (pauliY * pauliZ)
  suffices hT : T = 0 by simpa [T] using hT
  have ht : T = -T := by
    dsimp [T]
    calc
      LinearMap.trace Complex QubitSpace (pauliY * pauliZ)
          = LinearMap.trace Complex QubitSpace (-(pauliZ * pauliY)) := by rw [hanti]
      _ = -LinearMap.trace Complex QubitSpace (pauliZ * pauliY) := by simp
      _ = -LinearMap.trace Complex QubitSpace (pauliY * pauliZ) := by
            rw [LinearMap.trace_mul_comm Complex pauliZ pauliY]
  have hsum : T + T = 0 := eq_neg_iff_add_eq_zero.mp ht
  have htwo : (2 : Complex) * T = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
