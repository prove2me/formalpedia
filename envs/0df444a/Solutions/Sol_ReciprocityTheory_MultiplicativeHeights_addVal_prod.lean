-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:47.392799+00:00
-- url     : https://prove2.me/submissions/6e90e3d8-8810-4308-937d-444514f4467a

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Lemmata_GeneralBFactLast_Imports
import Definitions.Def_Lemmata_GeneralBFactTail_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetSubtypeCompAssociatedProd
import Theorems.Thm_Bl_general_b_fact_tail_goal1
import Theorems.Thm_P2M_RH_P2M_Bl_general_b_fact________goal1_21b1a474250b_b320b26946e406da


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module Submodule
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  first | exact Bl.general_b_fact'''''''.goal1 .. | (apply Bl.general_b_fact'''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''''''.goal1 <;> assumption)
end ReciprocityTheory.MultiplicativeHeights
