-- Prove2me | solution 1 for QEC.Distillation.isClosed_specialUnitaryGeneratedClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:09:05.205605+00:00
-- url     : https://prove2.me/submissions/388af51a-eb5a-4b22-a211-428591c16f93

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
    (generators : Set SingleQubitGate) :
    IsClosed (specialUnitaryGeneratedClosure generators : Set SingleQubitSpecialUnitary) := by
  change IsClosed
    ((determinantOneSubgroup.subtype :
      SingleQubitSpecialUnitary → SingleQubitGate) ⁻¹'
      ((generatedUnitarySubgroup generators).topologicalClosure : Set SingleQubitGate))
  exact (Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val
end QEC.Distillation
