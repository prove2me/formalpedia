-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.h_subsingleton_of_divisible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:50:25.93181+00:00
-- url     : https://prove2.me/submissions/35bedaf9-f3fd-4899-85ba-c99280e6fb37

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_h_subsingleton_of_uniquely_divisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : TRep ℤ G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) :=
  h_subsingleton_of_uniquely_divisible G M hM n hn
end ReciprocityTheory.DiscreteGroups.LocalClassField
