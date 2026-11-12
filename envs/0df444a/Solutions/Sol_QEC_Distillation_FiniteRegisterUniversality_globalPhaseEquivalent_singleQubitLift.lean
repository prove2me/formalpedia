-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.globalPhaseEquivalent_singleQubitLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:52:55.258097+00:00
-- url     : https://prove2.me/submissions/78d7df09-afec-468b-bde0-16373cea0fb3

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
theorem _root_.solution (wire : Wire)
    {left right : UnitaryGate (Fin 2)}
    (hphase : GlobalPhaseEquivalent left right) :
    GlobalPhaseEquivalent (singleQubitLift wire left) (singleQubitLift wire right) := by
  rcases hphase with ⟨scalar, hnorm, hmatrix⟩
  refine ⟨scalar, hnorm, ?_⟩
  change Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
      ((right : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
        (1 : Matrix (Bitstring (OtherWires wire))
          (Bitstring (OtherWires wire)) Complex)) =
    scalar • Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
      ((left : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
        (1 : Matrix (Bitstring (OtherWires wire))
          (Bitstring (OtherWires wire)) Complex))
  rw [hmatrix, Matrix.smul_kronecker]
  rfl
end QEC.Distillation.FiniteRegisterUniversality
