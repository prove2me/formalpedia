-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:04:22.078653+00:00
-- url     : https://prove2.me/submissions/6b1d873d-b9c8-4bf9-9c4e-d6d53297ecfb

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_finiteRegisterCircuit_has_projectiveClosureRepresentative
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_approximatesModuloPhase_of_globalPhaseEquivalent_mem_generatedUnitaryTopologicalClosure


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
theorem _root_.solution
    (generators : Set (UnitaryGate (Fin 2)))
    (hdense : ProjectivelyGeneratedDense generators)
    (circuit : FiniteRegisterCircuit Wire) (precision : Real) (hprecision : 0 < precision) :
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) generators) circuit.unitary precision := by
  rcases finiteRegisterCircuit_has_projectiveClosureRepresentative
    generators hdense circuit with
    ⟨representative, hrepresentative, hphase⟩
  exact approximatesModuloPhase_of_globalPhaseEquivalent_mem_generatedUnitaryTopologicalClosure
    hphase hrepresentative hprecision
end QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit
