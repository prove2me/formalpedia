-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.mem_rzPropagation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:46:19.035638+00:00
-- url     : https://prove2.me/submissions/ae729f8c-4cd1-4b18-ae05-2463e0c8ba2b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rzBlockOwner_mem
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rzBlockOwner_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (h : ¬ i.val % 2 = 0)
    (A : Finset (FamilyZ S depth i.succ)) (z : FamilyZ S depth i.castSucc) :
    z ∈ rzPropagation S depth i h A ↔
      ∃ p ∈ A, p ∈ (rzData S depth i h).coarseRegion z := by
  constructor
  · intro hz
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hz
    exact ⟨p,hp,he ▸ rzBlockOwner_mem S depth i h p⟩
  · rintro ⟨p,hp,hz⟩
    exact Finset.mem_image.mpr ⟨p,hp,rzBlockOwner_eq S depth i h p z hz⟩
end QEC.Coding.BDL26HistorySyndromeSensitivity
