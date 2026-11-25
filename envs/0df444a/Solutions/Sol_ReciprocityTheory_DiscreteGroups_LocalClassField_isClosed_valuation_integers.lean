-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isClosed_valuation_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:36.198512+00:00
-- url     : https://prove2.me/submissions/eb8544c8-15f8-4835-a77c-6d20c89acd9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ValuativeRel Function Filter Topology
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution : IsClosed (𝒪[K] : Set K) := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact Valued.isClosed_integer K
end ReciprocityTheory.DiscreteGroups.LocalClassField
