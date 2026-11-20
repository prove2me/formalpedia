-- Prove2me | solution 1 for QEC.Bounds.SourceFactorization.eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:53:17.171242+00:00
-- url     : https://prove2.me/submissions/8cdbcd98-988d-4cc2-889e-afbe04c1a31d

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
namespace SourceFactorization
theorem _root_.solution
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    {P A B : Semantics.Operator H} {coefficient : Complex}
    (h : SourceFactorization P A B coefficient) :
    P * A * B * P = coefficient • (P * B * P) :=
  h
end SourceFactorization
end QEC.Bounds
