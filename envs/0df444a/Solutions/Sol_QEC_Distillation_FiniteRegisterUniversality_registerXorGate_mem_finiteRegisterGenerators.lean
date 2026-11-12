-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.registerXorGate_mem_finiteRegisterGenerators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:54:52.479361+00:00
-- url     : https://prove2.me/submissions/82fa4574-6211-45da-9312-b44d4d9305a2

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
theorem _root_.solution
    (generators : Set (UnitaryGate (Fin 2))) (control target : Wire)
    (hdistinct : control ≠ target) :
    registerXorGate control target hdistinct ∈ finiteRegisterGenerators generators :=
  Or.inr ⟨control, target, hdistinct, rfl⟩
end QEC.Distillation.FiniteRegisterUniversality
