-- Prove2me | solution 2 for QEC.Semantics.PartialTraceRight.map_positive_operator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:34.437337+00:00
-- url     : https://prove2.me/submissions/b868a942-1f6b-41c2-bc2c-ad5205d8dac4

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.PartialTraceRight
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.PartialTraceRight
theorem _root_.solution (tr : PartialTraceRight H K) {A : Operator (CompositeSystem H K)}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (tr A) :=
  tr.map_positive hA
end QEC.Semantics.PartialTraceRight
