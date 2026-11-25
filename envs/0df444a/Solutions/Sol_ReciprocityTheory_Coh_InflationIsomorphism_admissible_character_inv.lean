-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.admissible_character_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:46.3645+00:00
-- url     : https://prove2.me/submissions/e9a0c82e-7e59-4c1c-b8a6-2658f9bc925f

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIso
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_emb_disc
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_iCG_inj
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_invPair_u
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_inv_lift
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_pLin_eq_zero
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
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]
namespace ReciprocityTheory.Coh.InflationIsomorphism
theorem _root_.solution (hN : IsClosed (N : Set G)) (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (M : TRep R G) [DiscreteTopology M.V] {Q : TRep R (G ⧸ N)} {P : Pair Q M} (hP : IsInvRep M N Q P)
    {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)} (hC : IsInvRep (CG M) N QC PC)
    {QQ : TRep R (G ⧸ N)} {PQ : Pair QQ (QG M)} (hQ : IsInvRep (QG M) N QQ PQ) :
    admitted (invPair hP hC (iCG M) (iCG_equiv M))
      (invPair hC hQ (pLin M) (pLin_equiv M)) := by
  have := inv_disc hP
  have := inv_disc hC
  have := inv_disc hQ
  refine ⟨rfl, rfl, emb_disc _ fun a b h => ?_, fun c => ?_, ?_⟩
  · have h' := congrArg PC.u h
    rw [invPair_u, invPair_u] at h'
    exact hP.2.1.injective (iCG_inj M h')
  · constructor
    · intro hc
      have h1 := congrArg PQ.u hc
      rw [invPair_u, map_zero, pLin_eq_zero] at h1
      obtain ⟨m, hm⟩ := h1
      have hmN : ∀ g ∈ N, M.rho g m = m := fun g hg => iCG_inj M (by
        rw [iCG_equiv, hm, inv_mem hC c g hg])
      obtain ⟨q, rfl⟩ := (hP.2.2 m).2 hmN
      refine ⟨q, hC.2.1.injective ?_⟩
      rw [invPair_u, hm]
    · rintro ⟨q, rfl⟩
      apply hQ.2.1.injective
      rw [invPair_u, invPair_u, map_zero, pLin_eq_zero]
      exact ⟨_, rfl⟩
  · have hs : Surjective (invPair hC hQ (pLin M) (pLin_equiv M)).u := by
      intro y
      obtain ⟨c, hcN, hc⟩ := inv_lift (R := R) N hN hW (CG M) (QG M) (pLin M)
        (pLin_equiv M) (pLin_surj M) (PQ.u y) (inv_mem hQ y)
      obtain ⟨c', rfl⟩ := (hC.2.2 c).2 hcN
      exact ⟨c', hQ.2.1.injective (by rw [invPair_u, hc])⟩
    exact ⟨surjInv hs, continuous_of_discreteTopology, surjInv_eq hs⟩
end ReciprocityTheory.Coh.InflationIsomorphism
