-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_compose_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:56:52.191784+00:00
-- url     : https://prove2.me/submissions/64e052be-c5a3-44b3-8615-7f2ffff5d390

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitarySubgroup_compose_mem


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (theta : Real)
    {U V : UnitaryGate (Fin 2)}
    (hU : U ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta))
    (hV : V ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta)) :
    U * V ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  generatedUnitarySubgroup_compose_mem (cliffordPhaseGenerators theta) hU hV
end QEC.Distillation.OneQubitMagic
