-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurentUnit_of_orderUnit_and_buildingIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:45:14.515377+00:00
-- url     : https://prove2.me/submissions/a169b060-bf18-4ae4-9800-3aac32ae0b4e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewFaithfulness
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_OrderUnitReconstruction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_of_order_and_buildingIntegral
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (u : CartwrightStegerOrder P r)))
    (hlocalInv : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
              CartwrightStegerOrder P r))) :
    ∃ v : (CartwrightStegerSkewLaurentRing P r)ˣ,
      skewLaurentToGlobalMatrix P r v =
        (cartwrightStegerOrderToCyclicAlgebra P r
          (u : CartwrightStegerOrder P r)).1 := by
  obtain ⟨f, hf⟩ := exists_skewLaurent_of_order_and_buildingIntegral
    P r (u : CartwrightStegerOrder P r) hlocal
  obtain ⟨g, hg⟩ := exists_skewLaurent_of_order_and_buildingIntegral
    P r ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
      CartwrightStegerOrder P r) hlocalInv
  have hfg : f * g = 1 := by
    apply skewLaurentToGlobalMatrix_injective P r
    rw [map_mul, hf, hg, map_one]
    have hu : (u : CartwrightStegerOrder P r) *
        ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
          CartwrightStegerOrder P r) = 1 := u.val_inv
    exact congrArg Subtype.val
      (congrArg (cartwrightStegerOrderToCyclicAlgebra P r) hu)
  have hgf : g * f = 1 := by
    apply skewLaurentToGlobalMatrix_injective P r
    rw [map_mul, hf, hg, map_one]
    have hu : ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
        CartwrightStegerOrder P r) *
        (u : CartwrightStegerOrder P r) = 1 := u.inv_val
    exact congrArg Subtype.val
      (congrArg (cartwrightStegerOrderToCyclicAlgebra P r) hu)
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
