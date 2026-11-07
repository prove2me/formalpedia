-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.expansionCutoff_eventMass_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:30:48.788385+00:00
-- url     : https://prove2.me/submissions/5baecb48-2e7b-4744-bb5e-cd3f3f704eb9

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_smallNeighborhood_eventMass_le_exp

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
          (checkSetNeighborhood sample S).card ≤
            expansionCutoff Delta S) ≤
      ENNReal.ofReal
        (Real.exp (-((Delta : Real) * S.card / 1000))) := by
  have hCutoffNat :
      expansionCutoff Delta S * 100 ≤ 92 * Delta * S.card := by
    exact Nat.div_mul_le_self (92 * Delta * S.card) 100
  have hCutoffReal :
      (expansionCutoff Delta S : Real) * 100 ≤
        92 * (Delta : Real) * S.card := by
    exact_mod_cast hCutoffNat
  calc
    _ ≤ ENNReal.ofReal
        (Real.exp
          ((expansionCutoff Delta S : Real) / 19 -
            (399997 : Real) * Delta * S.card / 8000000)) :=
      smallNeighborhood_eventMass_le_exp
        r Delta hr hDelta S hSmall (expansionCutoff Delta S)
    _ ≤ ENNReal.ofReal
        (Real.exp (-((Delta : Real) * S.card / 1000))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp_of_le
      have hDeltaNonneg : (0 : Real) ≤ Delta := by positivity
      have hCardNonneg : (0 : Real) ≤ S.card := by positivity
      nlinarith
end QEC.Coding.FiberBundle.RandomBase
