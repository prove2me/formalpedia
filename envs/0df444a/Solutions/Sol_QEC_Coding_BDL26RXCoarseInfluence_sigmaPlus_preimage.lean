-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.sigmaPlus_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:11:26.347624+00:00
-- url     : https://prove2.me/submissions/b524bbd2-d779-416a-938b-44894254a509

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCoarseInfluence
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    ∃ e : (indexedFamily S depth).Cochain1 i.succ,
      (indexedFamily S depth).coboundary1 i.succ e = sigma.val ∧
      (indexedFamily S depth).coboundary1 i.succ (e + canonicalBasisWord q) =
        (sigmaPlus S depth i sigma q).val := by
  obtain ⟨e, he⟩ := sigma.property
  refine ⟨e, he, ?_⟩
  change (indexedFamily S depth).coboundary1 i.succ (e + canonicalBasisWord q) =
    sigma.val + (indexedFamily S depth).coboundary1 i.succ (canonicalBasisWord q)
  rw [map_add, he]
end QEC.Coding.BDL26RXCoarseInfluence
