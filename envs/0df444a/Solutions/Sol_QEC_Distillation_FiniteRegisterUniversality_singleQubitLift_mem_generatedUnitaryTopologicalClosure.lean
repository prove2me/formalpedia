-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.singleQubitLift_mem_generatedUnitaryTopologicalClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:59:07.624238+00:00
-- url     : https://prove2.me/submissions/e2eb9474-6595-4188-8732-f6816404bc7f

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_continuous_singleQubitLift
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_singleQubitLift_mapsTo_generatedUnitarySubgroup

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
    (generators : Set (UnitaryGate (Fin 2))) (wire : Wire)
    {gate : UnitaryGate (Fin 2)}
    (hgate : gate ∈ generatedUnitaryTopologicalClosure generators) :
    singleQubitLift wire gate ∈
      generatedUnitaryTopologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators) :=
  map_mem_closure (continuous_singleQubitLift wire) hgate
    (singleQubitLift_mapsTo_generatedUnitarySubgroup generators wire)
end QEC.Distillation.FiniteRegisterUniversality
