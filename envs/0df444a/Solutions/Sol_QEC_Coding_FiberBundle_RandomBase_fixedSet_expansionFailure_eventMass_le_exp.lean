-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.fixedSet_expansionFailure_eventMass_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:21.701206+00:00
-- url     : https://prove2.me/submissions/69f08b23-31a7-4ede-8587-7f0267de7bb6

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_le_expansionCutoff_of_strict
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_mono
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_expansionCutoff_eventMass_le_exp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          100 * (checkSetNeighborhood sample S).card <
            92 * Delta * S.card) ≤
      ENNReal.ofReal
        (Real.exp (-((Delta : Real) * S.card / 1000))) := by
  calc
    _ ≤ eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤
            expansionCutoff Delta S) := by
      apply eventMass_mono
      intro sample hStrict
      exact card_le_expansionCutoff_of_strict hStrict
    _ ≤ _ := expansionCutoff_eventMass_le_exp
      r Delta hr hDelta S hSmall
end QEC.Coding.FiberBundle.RandomBase
