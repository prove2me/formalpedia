-- Prove2me | solution 1 for QEC.Distillation.mem_specialUnitaryGeneratedClosure_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:20:36.952475+00:00
-- url     : https://prove2.me/submissions/8e0c9a49-6d7f-4572-9968-4a055f483f0a

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality
namespace QEC.Distillation
theorem _root_.solution
    (generators : Set SingleQubitGate) (U : SingleQubitSpecialUnitary) :
    U ∈ specialUnitaryGeneratedClosure generators ↔
      (U : SingleQubitGate) ∈ generatedUnitaryTopologicalClosure generators :=
  Iff.rfl
end QEC.Distillation
