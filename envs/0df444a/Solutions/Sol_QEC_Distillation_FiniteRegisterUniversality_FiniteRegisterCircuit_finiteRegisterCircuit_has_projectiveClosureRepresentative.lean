-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.finiteRegisterCircuit_has_projectiveClosureRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:01:57.48981+00:00
-- url     : https://prove2.me/submissions/805f83d8-01cf-436f-831c-dbd78798d265

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_globalPhaseEquivalent_singleQubitLift
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_registerXorGate_mem_finiteRegisterGenerators
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_singleQubitLift_mem_generatedUnitaryTopologicalClosure
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitarySubgroup_subset_topologicalClosure
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_mul
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_refl


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
    (circuit : FiniteRegisterCircuit Wire) :
    ∃ representative : UnitaryGate (Bitstring Wire),
      representative ∈ generatedUnitaryTopologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators) ∧
      GlobalPhaseEquivalent circuit.unitary representative := by
  induction circuit with
  | identity =>
      refine ⟨1, ?_, globalPhaseEquivalent_refl 1⟩
      exact generatedUnitarySubgroup_subset_topologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators)
        (generatedUnitarySubgroup
          (finiteRegisterGenerators (Wire := Wire) generators)).one_mem
  | oneQubit wire gate =>
      rcases hdense gate with ⟨representative, hrepresentative, hphase⟩
      refine ⟨singleQubitLift wire representative, ?_, ?_⟩
      · exact singleQubitLift_mem_generatedUnitaryTopologicalClosure generators wire
          hrepresentative
      · exact globalPhaseEquivalent_singleQubitLift wire hphase
  | xor control target hdistinct =>
      refine ⟨registerXorGate control target hdistinct, ?_,
        globalPhaseEquivalent_refl _⟩
      apply generatedUnitarySubgroup_subset_topologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators)
      exact Subgroup.subset_closure
        (registerXorGate_mem_finiteRegisterGenerators generators control target hdistinct)
  | compose first second hfirst hsecond =>
      rcases hfirst with ⟨firstRepresentative, hfirstMem, hfirstPhase⟩
      rcases hsecond with ⟨secondRepresentative, hsecondMem, hsecondPhase⟩
      refine ⟨secondRepresentative * firstRepresentative, ?_, ?_⟩
      · change secondRepresentative * firstRepresentative ∈
          (generatedUnitarySubgroup
            (finiteRegisterGenerators (Wire := Wire) generators)).topologicalClosure
        exact (generatedUnitarySubgroup
          (finiteRegisterGenerators (Wire := Wire) generators)).topologicalClosure.mul_mem
            hsecondMem hfirstMem
      · exact globalPhaseEquivalent_mul hsecondPhase hfirstPhase
end QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit
