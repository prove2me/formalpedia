-- Prove2me | solution 1 for PositivityTheory.CW.group_facts_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:29.302445+00:00
-- url     : https://prove2.me/submissions/3673fb89-e1dc-48d4-b614-c3bc9dbbec00

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GroupFactsHolds
import Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_mul_mem
import Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_hilbert_schmidt_continuous
import Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_compact
import Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_Xp_inP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_exp_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : UnitaryGroupFacts := by
  intro n ε
  refine ⟨CompactGroupFacts.compact ε, ?_, ?_, ?_, CompactGroupFacts.hilbert_schmidt_continuous, CompactGroupFacts.Xp_inP ε⟩
  · show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  · intro g hg X hX t
    refine CompactGroupFacts.mul_mem ε hg ?_
    have := rq_exp_mem ε X hX.1 t
    rwa [Complex.coe_smul] at this
  · intro X s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left s |>.smul_right t)
end PositivityTheory.CW
