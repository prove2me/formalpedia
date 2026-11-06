-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliZ_pauliX_trace
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:43:31.203692+00:00
-- url     : https://prove2.me/submissions/810831c4-ec56-42cd-9192-6e7e6f5698de

-- ID: fcfb144f-6479-4a72-a877-23fcc7254031 | NAME: QEC.Semantics.Qubit.pauliZ_pauliX_trace | 未本地编译验证
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
