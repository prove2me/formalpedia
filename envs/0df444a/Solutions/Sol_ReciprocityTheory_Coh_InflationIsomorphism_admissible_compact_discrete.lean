-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.admissible_compact_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:46:14.234086+00:00
-- url     : https://prove2.me/submissions/e5eb1421-d4e8-458c-bf9d-1f0f79505261

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_emb_disc
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_iCG_inj
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_pLin_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
open ReciprocityTheory.Coh.InflationIsomorphism
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
namespace ReciprocityTheory.Coh.InflationIsomorphism
theorem _root_.solution [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : admitted (iP M) (pP M) where
  i_id := rfl
  p_id := rfl
  emb := emb_disc _ (iCG_inj M)
  exact := LinearMap.exact_map_mkQ_range _
  sec := ⟨surjInv (pLin_surj M), continuous_of_discreteTopology,
    surjInv_eq _⟩
end ReciprocityTheory.Coh.InflationIsomorphism
