-- Prove2me | solution 1 for QEC.Semantics.OperatorMatrix.matrixUnit_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:53:52.670247+00:00
-- url     : https://prove2.me/submissions/0fbe9ab9-4aa5-44a2-a08b-661b94fd2ceb

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.OperatorMatrix
theorem _root_.solution (b : OrthonormalBasis (Fin n) Complex H) (i j : Fin n) :
    LinearMap.adjoint (matrixUnit b i j) = matrixUnit b j i := by
  haveI := FiniteDimensional.complete Complex H
  change LinearMap.adjoint ((InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) =
    (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  exact congrArg ContinuousLinearMap.toLinearMap
    (InnerProductSpace.adjoint_rankOne (𝕜 := Complex) (b i) (b j))
end QEC.Semantics.OperatorMatrix
