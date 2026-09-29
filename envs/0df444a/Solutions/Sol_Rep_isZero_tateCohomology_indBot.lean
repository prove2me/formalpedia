-- Prove2me | solution 1 for Rep.isZero_tateCohomology_indBot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8ca3dd85-8fba-5a51-be5f-5002f28cb25c

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_subsingleton_tateH0_ind_bot
import Theorems.Thm_Rep_subsingleton_tateHneg1_ind_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_isZero_tateCohomology_indBot

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (A.indBot.tateCohomology q) := by
  classical
  let B : Rep.{u} k (⊥ : Subgroup G) := Rep.res (⊥ : Subgroup G).subtype A
  rcases q with (_ | n) | (_ | n)
  ·
    show CategoryTheory.Limits.IsZero (ModuleCat.of k A.indBot.tateH0)
    haveI : Subsingleton A.indBot.tateH0 := Rep.subsingleton_tateH0_ind_bot B
    exact ModuleCat.isZero_of_subsingleton _
  ·
    show CategoryTheory.Limits.IsZero (groupCohomology A.indBot (n + 1))
    refine (isZero_groupCohomology_succ_of_subsingleton B n).of_iso ?_
    exact (groupCohomology.functor k G (n + 1)).mapIso (Rep.indCoindIso B) ≪≫ groupCohomology.coindIso B (n + 1)
  ·
    show CategoryTheory.Limits.IsZero (ModuleCat.of k A.indBot.tateHneg1)
    haveI : Subsingleton A.indBot.tateHneg1 := Rep.subsingleton_tateHneg1_ind_bot B
    exact ModuleCat.isZero_of_subsingleton _
  ·
    show CategoryTheory.Limits.IsZero (groupHomology A.indBot (n + 1))
    exact (isZero_groupHomology_succ_of_subsingleton B n).of_iso (groupHomology.indIso (⊥ : Subgroup G) B (n + 1))

end S_Rep_isZero_tateCohomology_indBot
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_indBot (solution)
