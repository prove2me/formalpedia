-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_split__augClass_80c011573ab3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:35.445057+00:00
-- url     : https://prove2.me/submissions/588ce8ad-96c6-48f8-b4f4-f5cfb0282f67

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_P2M_GroundTheory_GroupCoh___splittingSES_res____76acf067f5e4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]
omit [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution : splitδ M u S (augClass S) = resClass M u S :=
  δ_splittingSES_res_δ₀ M u S.subtype
end GroundTheory.GroupCoh
