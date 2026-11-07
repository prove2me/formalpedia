-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_hasUpperUnipotentInfinityConjugation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:25.777145+00:00
-- url     : https://prove2.me/submissions/f588cfe3-e786-45f9-8201-eb34b54fa2a8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_conj_monomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    HasUpperUnipotentInfinityConjugation P r
      (cartwrightStegerGenerator P r x) := by
  intro k ζ
  let coeff : ℕ → ConstantExtension P r := fun i =>
    infinityConjugationCoefficient P r
        (constantClassRepresentative P r x) (k : ℕ) ζ *
      (infinityCyclicCoefficient P r
        (constantClassRepresentative P r x) i : ConstantExtension P r)
  refine ⟨coeff, coeff, ?_⟩
  rw [cartwrightStegerGenerator_conj_monomial]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
