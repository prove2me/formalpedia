-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_inverse_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:17:47.613732+00:00
-- url     : https://prove2.me/submissions/84da7a86-f029-4f03-8cf3-18a751cc0e51

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (theta : Real)
    {U : UnitaryGate (Fin 2)}
    (hU : U ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta)) :
    U⁻¹ ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  (generatedUnitarySubgroup (cliffordPhaseGenerators theta)).inv_mem hU
end QEC.Distillation.OneQubitMagic
