-- Prove2me | solution 1 for QEC.Bounds.unitary_conjOperator_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:53:21.286547+00:00
-- url     : https://prove2.me/submissions/046d1ea6-28f2-4545-8e55-a8d4d78e4518

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
namespace QEC.Bounds
theorem _root_.solution
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (U : Semantics.UnitaryTransport H H) {P Q : Semantics.Operator H} (h : P = Q) :
    U.conjOperator P = U.conjOperator Q := by
  subst Q
  rfl
end QEC.Bounds
