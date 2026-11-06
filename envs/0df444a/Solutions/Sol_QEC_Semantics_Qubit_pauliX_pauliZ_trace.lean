-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliX_pauliZ_trace
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:43:24.179187+00:00
-- url     : https://prove2.me/submissions/d589146e-cbf7-4ca8-904b-2f784ed170d1

-- ID: 71a3aead-2ea5-47ef-9554-86e9f1d0dddc | NAME: QEC.Semantics.Qubit.pauliX_pauliZ_trace | 未本地编译验证
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
    LinearMap.trace Complex QubitSpace (pauliX * pauliZ) = 0 := by
  have hanti : pauliX * pauliZ = -(pauliZ * pauliX) := by
    ext ψ b
    fin_cases b <;>
      simp [Module.End.mul_apply, pauliX_apply, pauliZ_apply, zPhase] <;> ring
  let T := LinearMap.trace Complex QubitSpace (pauliX * pauliZ)
  suffices hT : T = 0 by simpa [T] using hT
  have ht : T = -T := by
    dsimp [T]
    calc
      LinearMap.trace Complex QubitSpace (pauliX * pauliZ)
          = LinearMap.trace Complex QubitSpace (-(pauliZ * pauliX)) := by rw [hanti]
      _ = -LinearMap.trace Complex QubitSpace (pauliZ * pauliX) := by simp
      _ = -LinearMap.trace Complex QubitSpace (pauliX * pauliZ) := by
            rw [LinearMap.trace_mul_comm Complex pauliZ pauliX]
  have hsum : T + T = 0 := eq_neg_iff_add_eq_zero.mp ht
  have htwo : (2 : Complex) * T = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
