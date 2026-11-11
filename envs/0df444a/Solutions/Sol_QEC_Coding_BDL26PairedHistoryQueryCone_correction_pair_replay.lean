-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.correction_pair_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:37:54.81969+00:00
-- url     : https://prove2.me/submissions/c28498cb-cb26-4cce-85de-0e91e3df9099

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_component_agreement
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_correction_eq_components
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_component_pair_zero

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
    (s t s' t' : (indexedFamily S depth).Syndrome i.succ)
    (hs : hammingSupport (s.val+t.val) ⊆ U)
    (hs' : hammingSupport (s'.val+t'.val) ⊆ U)
    (ha : AgreeOn (correctionQueries S depth i U) s.val s'.val)
    (hb : AgreeOn (correctionQueries S depth i U) t.val t'.val) :
    (actualStep S depth i s).correction + (actualStep S depth i t).correction =
      (actualStep S depth i s').correction + (actualStep S depth i t').correction := by
  simp_rw [correction_eq_components,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ affected S depth i U
  · have hsub : ownerRead S depth i v ⊆ correctionQueries S depth i U :=
      fun p hp => Finset.mem_biUnion.mpr ⟨v,hv,hp⟩
    rw [component_agreement S depth i v s.val s'.val (fun p hp => ha p (hsub hp)),
      component_agreement S depth i v t.val t'.val (fun p hp => hb p (hsub hp))]
  · rw [component_pair_zero S depth i U s.val t.val hs v hv,
      component_pair_zero S depth i U s'.val t'.val hs' v hv]
end QEC.Coding.BDL26PairedHistoryQueryCone
