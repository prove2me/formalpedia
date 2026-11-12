-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderInnerFormToOrderUnits_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:46:57.509935+00:00
-- url     : https://prove2.me/submissions/b56cf9c7-9563-4f11-9186-4afd24e5532d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderSplitCoordinate_to_global

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderInnerFormToOrderUnits P r) := by
  intro u
  let A := cartwrightStegerOrderSplitCoordinate P r
    (u : CartwrightStegerOrder P r)
  let B := cartwrightStegerOrderSplitCoordinate P r
    ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) : CartwrightStegerOrder P r)
  have hA : A.map (constantArithmeticToSplittingFunctionField P r) = u :=
    cartwrightStegerOrderSplitCoordinate_to_global P r
      (u : CartwrightStegerOrder P r)
  have hB : B.map (constantArithmeticToSplittingFunctionField P r) = u⁻¹ :=
    cartwrightStegerOrderSplitCoordinate_to_global P r
      ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) : CartwrightStegerOrder P r)
  have hA' :
      (constantArithmeticToSplittingFunctionField P r).mapMatrix A =
        ((u : CartwrightStegerOrder P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := hA
  have hB' :
      (constantArithmeticToSplittingFunctionField P r).mapMatrix B =
        (((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
          CartwrightStegerOrder P r) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (SplittingFunctionField P r)) := hB
  have mapMatrix_injective : Function.Injective
      ((constantArithmeticToSplittingFunctionField P r).mapMatrix :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r) →
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by
    intro M N hMN
    ext i j
    apply constantArithmeticToSplittingFunctionField_injective P r
    exact congrArg (fun X => X i j) hMN
  have hAB : A * B = 1 := by
    apply mapMatrix_injective
    rw [map_mul, map_one, hA', hB']
    exact congrArg Subtype.val u.val_inv
  have hBA : B * A = 1 := by
    apply mapMatrix_injective
    rw [map_mul, map_one, hB', hA']
    exact congrArg Subtype.val u.inv_val
  let gGL : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
    { val := A
      inv := B
      val_inv := hAB
      inv_val := hBA }
  have hg : gGL ∈ OrderInnerFormUnits P r := by
    constructor
    · change A.map (constantArithmeticToSplittingFunctionField P r) ∈
          CartwrightStegerOrder P r
      rw [hA]
      exact (u : CartwrightStegerOrder P r).property
    · change B.map (constantArithmeticToSplittingFunctionField P r) ∈
          CartwrightStegerOrder P r
      rw [hB]
      exact ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
        CartwrightStegerOrder P r).property
  let g : OrderInnerFormUnits P r := ⟨gGL, hg⟩
  refine ⟨g, ?_⟩
  apply Units.ext
  apply Subtype.ext
  exact hA
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
