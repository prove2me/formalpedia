-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalAugmentation_ne_zero_of_homologyProjection_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:47.566713+00:00
-- url     : https://prove2.me/submissions/f3120175-de2b-4970-abbb-049e672c040f

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v
namespace QEC.Coding.BalancedProduct.HorizontalSubsystem
theorem _root_.solution
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A x)).middleCycleCode.carrier)
    (hProjected : horizontalHomologyProjection A x
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).middleBoundaryInCycles.mkQ
          ⟨z, hz⟩) ≠ 0) :
    horizontalAugmentation z ≠ 0 := by
  intro hzero
  apply hProjected
  rw [horizontalHomologyProjection,
    ThreeTermChainMap.inducedMiddleHomology_mk]
  have hMapped :
      (augmentationChainMap A x).mapMiddleCycle ⟨z, hz⟩ = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hMapped, map_zero]
end QEC.Coding.BalancedProduct.HorizontalSubsystem
