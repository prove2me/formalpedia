-- Prove2me | solution 1 for QEC.Semantics.PartialTraceRight.map_positive_operator
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:56:36.305734+00:00
-- url     : https://prove2.me/submissions/b842a592-4e2c-439a-9015-9afe60275d3e

-- ID: cda2fca8-809e-44f7-b6c7-96e298256b6c | NAME: QEC.Semantics.PartialTraceRight.map_positive_operator | 未本地编译验证
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

theorem solution (tr : PartialTraceRight H K) {A : Operator (CompositeSystem H K)}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (tr A) := by
  simpa using tr.map_positive hA
