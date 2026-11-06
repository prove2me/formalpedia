-- Prove2me | solution 1 for QEC.Semantics.OperatorMatrix.matrixUnit_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:54:03.698124+00:00
-- url     : https://prove2.me/submissions/1267e349-1b8b-4a7d-8250-6304e9d44a30

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
theorem _root_.solution (b : OrthonormalBasis (Fin n) Complex H) (i j : Fin n) (x : H) :
    matrixUnit b i j x = inner Complex (b j) x • b i :=
  rfl
end QEC.Semantics.OperatorMatrix
