-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.singleQubitLift_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:52:38.968448+00:00
-- url     : https://prove2.me/submissions/8ab8b0c6-00a5-424a-a0d8-9053cb60681f

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
theorem _root_.solution (wire : Wire) (gate : UnitaryGate (Fin 2)) :
    singleQubitLift wire gate⁻¹ = (singleQubitLift wire gate)⁻¹ :=
  (singleQubitLiftHom wire).map_inv gate
end QEC.Distillation.FiniteRegisterUniversality
