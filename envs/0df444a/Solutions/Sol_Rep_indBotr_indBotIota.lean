-- Prove2me | solution 1 for Rep.indBotr_indBotIota
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/72224f57-3ae3-573d-8ec3-15294b6796b4

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_indBotIota_apply
import Theorems.Thm_Rep_indBotr_indBotMk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_indBotr_indBotIota

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (a : A) :
    A.indBotr ((Rep.indBotι A).hom a) = a := by
  classical
  rw [Rep.indBotIota_apply, map_sum, Finset.sum_eq_single (1 : G)]
  · rw [Rep.indBotr_indBotMk, Finsupp.single_eq_same, one_smul, map_one, Module.End.one_apply]
  · intro g _ hg
    rw [Rep.indBotr_indBotMk, Finsupp.single_apply, if_neg hg, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

end S_Rep_indBotr_indBotIota
end P2MW
export P2MW.S_Rep_indBotr_indBotIota (solution)
