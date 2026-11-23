-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isClosedEmbedding_resGK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:06.02502+00:00
-- url     : https://prove2.me/submissions/5ff05734-3b28-428a-a1d3-d9b34bf67cbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_resGK_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) : Topology.IsClosedEmbedding (resGK h) :=
  (resGK_continuous h).isClosedEmbedding (resGK_injective h)
end ReciprocityTheory.DiscreteGroups.LocalClassField
