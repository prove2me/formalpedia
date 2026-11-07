-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:38:46.102084+00:00
-- url     : https://prove2.me/submissions/3ba9fb7d-ebb4-4cd2-bfba-5a9e7dc0a51d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_conj_monomial_shifted
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sum_infinityShiftedCorrectionTerm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_inv_splittingY_smul_add_splittingY_smul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (hk : k ≤ r.matrixRank) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k)) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityConjugationFormula P r u k ζ := by
  change
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        infinityLeadingMonomial P r k ζ) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) = _
  rw [constantConjugatedCartwrightStegerB_conj_monomial_shifted]
  rw [sum_infinityShiftedCorrectionTerm P r u k hk ζ]
  rw [inv_splittingY_smul_add_splittingY_smul]
  rw [infinityConjugationFormula, infinityLeadingMonomial]
  abel
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
