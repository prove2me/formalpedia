-- Prove2me | solution 1 for TunnellMap.incidentStream_eq_preferenceList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:22.34256+00:00
-- url     : https://prove2.me/submissions/561bc803-7f79-4772-94d1-5f0013df9137

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Theorems.Thm_TunnellMap_incidentStream_pairwise
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_nodup
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_pairwise
import Theorems.Thm_TunnellMap_OrderedGenerator_incidentStream_nodup
import Theorems.Thm_TunnellMap_OrderedGenerator_mem_incidentStream
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList



set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    incidentStream hnpos s F =
      (residualOrbitRanking hnpos).preferenceList
        ((bResidualInvolution n).orbit s) := by
  let I := residualOrbitRanking hnpos
  let q := (bResidualInvolution n).orbit s
  have hperm : (incidentStream hnpos s F).Perm (I.preferenceList q) := by
    apply (List.perm_ext_iff_of_nodup
      (incidentStream_nodup hnpos s F)
      (I.preferenceList_nodup q)).2
    intro t
    constructor
    · intro _
      exact I.mem_preferenceList q t
    · intro _
      exact mem_incidentStream hn hnpos s F t
  apply hperm.eq_of_pairwise
  · intro t₁ t₂ _ _ h₁₂ h₂₁
    exact I.source_injective q (le_antisymm h₁₂ h₂₁)
  · exact incidentStream_pairwise hnpos s F
  · exact I.preferenceList_pairwise q
end TunnellMap
