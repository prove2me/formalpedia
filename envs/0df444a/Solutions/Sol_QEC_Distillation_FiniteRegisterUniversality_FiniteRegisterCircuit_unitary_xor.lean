-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_xor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:59:44.629207+00:00
-- url     : https://prove2.me/submissions/10d4ecc2-9ff3-4a5c-a3a9-749aeee09f68

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
theorem _root_.solution (control target : Wire) (hdistinct : control ≠ target) :
    (xor control target hdistinct : FiniteRegisterCircuit Wire).unitary =
      registerXorGate control target hdistinct :=
  rfl
end QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit
