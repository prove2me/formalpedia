-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.familyHits_card_le_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:37:39.466522+00:00
-- url     : https://prove2.me/submissions/70a99191-d9aa-46fa-ad23-78db00a39411

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {ι κ E : Type*} [Fintype ι] [Fintype κ]
    (images : ι → Set E) (region : Set E) (cover : κ → Set E)
    (hcover : ∀ p ∈ region, ∃ k, p ∈ cover k) :
    (familyHits images region).card ≤ ∑ k, (familyHits images (cover k)).card := by
  classical
  have hsub : familyHits images region ⊆
      Finset.univ.biUnion (fun k => familyHits images (cover k)) := by
    intro i hi
    obtain ⟨p,hpi,hpr⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨k,hpk⟩ := hcover p hpr
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hpi,hpk⟩⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
end QEC.Coding.BDL26RandomPerturbation
