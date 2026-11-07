-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_conj_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:40:53.958714+00:00
-- url     : https://prove2.me/submissions/e96de35b-7ec5-4b53-9007-fda70072d4a3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_eq_constantConjugatedB
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_conj_monomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r)
    (k : Fin r.matrixRank) (ζ : ConstantExtension P r) :
    ((cartwrightStegerGenerator P r x :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ))) *
        (((cartwrightStegerGenerator P r x)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityConjugationFormula P r
        (constantClassRepresentative P r x) (k : ℕ) ζ := by
  rw [cartwrightStegerGenerator_eq_constantConjugatedB]
  exact constantConjugatedCartwrightStegerB_conj_monomial P r
    (constantClassRepresentative P r x) (k : ℕ)
    (Nat.le_of_lt k.isLt) ζ
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
