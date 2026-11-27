-- Prove2me | solution 1 for P2M_GroundTheory_LocalField_isUnramifiedSubextension_iff__8ebb20d89f29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:31.168628+00:00
-- url     : https://prove2.me/submissions/48d061e2-2c20-44a8-ac0c-78fc558c9652

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
import Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_TameExtension
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_ramificationIndex_eq_one
import Theorems.Thm_GroundTheory_LocalField_isUnramifiedSubextension_iff_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IsUnramifiedSubextension E ↔ ramificationIndex K E = 1 :=
  ⟨fun h ↦ h.ramificationIndex_eq_one, fun h ↦ (isUnramifiedSubextension_iff_exists E).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩
end GroundTheory.LocalField
