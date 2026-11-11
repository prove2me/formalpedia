-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_compose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:00:16.653236+00:00
-- url     : https://prove2.me/submissions/403f379b-12e3-4f70-a99e-534f305e1ac7

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
open QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit
variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]
namespace QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit
theorem _root_.solution (first second : FiniteRegisterCircuit Wire) :
    (compose first second).unitary = second.unitary * first.unitary :=
  rfl
end QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit
