-- Prove2me | solution 1 for QEC.Bounds.source_factorization_projector_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:49:47.518655+00:00
-- url     : https://prove2.me/submissions/e294de90-9a1a-400a-a857-05e2d62fe4d3

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
    (P Q A B : Semantics.Operator H) (coefficient : Complex)
    (hPQ : P = Q)
    (hfactor : SourceFactorization P A B coefficient) :
    SourceFactorization Q A B coefficient := by
  subst Q
  exact hfactor
end QEC.Bounds
