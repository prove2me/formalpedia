-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.continuous_retr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:07.754487+00:00
-- url     : https://prove2.me/submissions/1ef5c89e-19ae-4d0f-b6a5-b931b344de77

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Theorems.Thm_ReciprocityTheory_Coh_CCA_continuous_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution (hU : IsOpen (U : Set G)) : Continuous (retr U) :=
  Continuous.subtype_mk (continuous_id.mul (continuous_rep U hU).inv) _
end ReciprocityTheory.Coh.CCA
