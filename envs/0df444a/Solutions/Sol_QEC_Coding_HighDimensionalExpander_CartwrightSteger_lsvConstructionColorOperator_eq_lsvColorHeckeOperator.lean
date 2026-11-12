-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvConstructionColorOperator_eq_lsvColorHeckeOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:08:08.618269+00:00
-- url     : https://prove2.me/submissions/5b0b8b82-7f7a-42f6-b33a-ccd2357d0747

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_image_buildingColorGeneratorFinset_vertexMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_injective


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingVertexDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level color : Nat)
    (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    lsvConstructionColorOperator P r level color =
      lsvColorHeckeOperator P r level color := by
  classical
  apply LinearMap.ext
  intro f
  funext x
  rw [lsvColorHeckeOperator_apply]
  change (∑ s ∈ buildingColorGeneratorFinset P r color,
      f (x * buildingLatticeFiniteReduction P r level s)) =
    ∑ q ∈ fundamentalNeighborCosets (BaseField P) r.matrixRank color,
      f (x * buildingLatticeFiniteReduction P r level
        ((lsvBuildingLatticeVertexEquiv P r).symm q))
  rw [← image_buildingColorGeneratorFinset_vertexMap P r color hcolor]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [show (lsvBuildingLatticeVertexEquiv P r).symm
        (buildingLatticeVertexMap P r s) = s by
      exact (lsvBuildingLatticeVertexEquiv P r).symm_apply_apply s]
  · intro a ha b hb hab
    exact buildingLatticeVertexMap_injective P r hab
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
