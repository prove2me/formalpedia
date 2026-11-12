-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.continuous_singleQubitLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:52:42.173105+00:00
-- url     : https://prove2.me/submissions/96debf83-6ce1-4acd-bbdb-60f0b3a2bdfd

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality

set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteRegisterUniversality
open Semantics Semantics.Qubit
open GeneratedUniversality
open scoped Kronecker
variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]
namespace QEC.Distillation.FiniteRegisterUniversality
theorem _root_.solution (wire : Wire) :
    Continuous (singleQubitLift wire) := by
  apply Continuous.subtype_mk
  change Continuous (fun gate : UnitaryGate (Fin 2) =>
    singleQubitLiftMatrix wire (gate : Matrix (Fin 2) (Fin 2) Complex))
  exact (singleQubitLiftLinear wire).continuous_of_finiteDimensional.comp
    continuous_subtype_val
end QEC.Distillation.FiniteRegisterUniversality
