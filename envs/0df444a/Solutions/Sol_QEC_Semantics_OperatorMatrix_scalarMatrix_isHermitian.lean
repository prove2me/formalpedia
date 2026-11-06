-- Prove2me | solution 1 for QEC.Semantics.OperatorMatrix.scalarMatrix_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:32:25.771176+00:00
-- url     : https://prove2.me/submissions/aa5eeaea-684d-46dd-9d42-47ba6ab44c69

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.OperatorMatrix
theorem _root_.solution {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (hM : IsPositive M)
    (b : OrthonormalBasis β Complex H) :
    (scalarMatrix M b).IsHermitian := by
  classical
  refine Matrix.IsHermitian.ext ?_
  rintro ⟨i, p⟩ ⟨j, q⟩
  simp [scalarMatrix, hM.1 i j, LinearMap.adjoint_inner_right]
end QEC.Semantics.OperatorMatrix
