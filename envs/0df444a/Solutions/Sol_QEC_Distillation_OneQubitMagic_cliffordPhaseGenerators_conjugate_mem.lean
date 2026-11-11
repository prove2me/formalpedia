-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_conjugate_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:12:54.303303+00:00
-- url     : https://prove2.me/submissions/f54a98a5-2e1a-475c-b315-5075f4a1762d

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitarySubgroup_conjugate_mem


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
    U * V * U⁻¹ ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  generatedUnitarySubgroup_conjugate_mem (cliffordPhaseGenerators theta) hU hV
end QEC.Distillation.OneQubitMagic
