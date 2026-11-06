-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliX_pauliY_trace
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:48:32.454847+00:00
-- url     : https://prove2.me/submissions/f67cc5ba-7ee6-4f83-9691-87492cab5eb5

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
    LinearMap.trace Complex QubitSpace (pauliX * pauliY) = 0 := by
  have hanti : pauliX * pauliY = -(pauliY * pauliX) := by
    ext ψ b
    fin_cases b <;>
      simp [Module.End.mul_apply, pauliX_apply, pauliY_apply, flipBit]
  let T := LinearMap.trace Complex QubitSpace (pauliX * pauliY)
  suffices hT : T = 0 by simpa [T] using hT
  have ht : T = -T := by
    dsimp [T]
    calc
      LinearMap.trace Complex QubitSpace (pauliX * pauliY)
          = LinearMap.trace Complex QubitSpace (-(pauliY * pauliX)) := by rw [hanti]
      _ = -LinearMap.trace Complex QubitSpace (pauliY * pauliX) := by simp
      _ = -LinearMap.trace Complex QubitSpace (pauliX * pauliY) := by
            rw [LinearMap.trace_mul_comm Complex pauliY pauliX]
  have hsum : T + T = 0 := eq_neg_iff_add_eq_zero.mp ht
  have htwo : (2 : Complex) * T = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
