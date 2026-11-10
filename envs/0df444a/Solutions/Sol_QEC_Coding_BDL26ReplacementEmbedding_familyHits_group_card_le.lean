-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.familyHits_group_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:43:50.963672+00:00
-- url     : https://prove2.me/submissions/a4c4900a-fec6-4808-ad4b-af5dd0df19f4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*}
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution {A B : Type*} [Fintype A] [Fintype B]
    (images : A × B → Set E) (region : Set E) :
    (familyHits (fun a => ⋃ b, images (a, b)) region).card ≤
      (familyHits images region).card := by
  classical
  have hsub : familyHits (fun a => ⋃ b, images (a, b)) region ⊆
      (familyHits images region).image Prod.fst := by
    intro a ha
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hp.1
    exact Finset.mem_image.mpr ⟨(a, b),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hb, hp.2⟩⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)
end QEC.Coding.BDL26ReplacementEmbedding
