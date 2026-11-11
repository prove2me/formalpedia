-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.component_pair_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:30:55.579901+00:00
-- url     : https://prove2.me/submissions/933ee87d-d563-4c15-ada2-35e308bd580d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_binary_word_add_self
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_component_agreement
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_binary_add_eq_zero_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (U : Finset (FamilyZ S depth i.succ))
    (s t : Word BDL26Field (FamilyZ S depth i.succ))
    (hs : hammingSupport (s+t) ⊆ U) (v : Owners S depth i)
    (hv : v ∉ affected S depth i U) :
    component S depth i v s + component S depth i v t = 0 := by
  have he : component S depth i v s = component S depth i v t := by
    apply component_agreement S depth i v s t
    intro p hp
    apply (binary_add_eq_zero_iff _ _).mp
    by_contra hn
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hs
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩),hp⟩)
  rw [he]
  exact binary_word_add_self _
end QEC.Coding.BDL26PairedHistoryQueryCone
