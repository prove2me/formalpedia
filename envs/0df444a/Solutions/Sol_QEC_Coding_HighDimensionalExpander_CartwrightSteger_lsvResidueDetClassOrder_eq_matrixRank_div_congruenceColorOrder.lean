-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvResidueDetClassOrder_eq_matrixRank_div_congruenceColorOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:06:43.469277+00:00
-- url     : https://prove2.me/submissions/a0b56394-4e28-4a9f-9f83-cb8d2266cdb9

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvMatrixRank_eq_congruenceColorOrder_mul_residueDetClassOrder
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    r.matrixRank /
        Nat.card (lsvCongruenceBuildingColorImage P r level) =
      orderOf
        (QuotientGroup.mk (indexRatioUnit P r level) :
          ResiduePowerClass P r level) := by
  letI : NeZero r.matrixRank :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega)
      (Rank.two_le_matrixRank r))⟩
  letI : Finite (lsvCongruenceBuildingColorImage P r level) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let t := Nat.card (lsvCongruenceBuildingColorImage P r level)
  let quotientOrder := orderOf
    (QuotientGroup.mk (indexRatioUnit P r level) :
      ResiduePowerClass P r level)
  have hcard : r.matrixRank = t * quotientOrder :=
    lsvMatrixRank_eq_congruenceColorOrder_mul_residueDetClassOrder
      P r level hPSL
  calc
    r.matrixRank / t = (t * quotientOrder) / t :=
      congrArg (fun n ↦ n / t) hcard
    _ = quotientOrder := Nat.mul_div_cancel_left _ Nat.card_pos
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
