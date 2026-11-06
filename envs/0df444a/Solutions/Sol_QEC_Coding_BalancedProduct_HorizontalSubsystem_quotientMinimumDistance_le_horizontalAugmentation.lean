-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.HorizontalSubsystem.quotientMinimumDistance_le_horizontalAugmentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:45.375896+00:00
-- url     : https://prove2.me/submissions/9c647b53-e608-40ba-97e0-e8de4c2649ba

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_horizontalAugmentation_ne_zero_of_homologyProjection_ne_zero

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
    {d : Nat}
    (hMinimum : MinimumDistance
      (quotientTannerComplex A).middleCycleCode d)
    (hProjected : horizontalHomologyProjection A x
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).middleBoundaryInCycles.mkQ
          ⟨z, hz⟩) ≠ 0) :
    d ≤ HammingWeight (horizontalAugmentation z) := by
  rcases hMinimum with ⟨_witness, _hwitnessMem, _hwitnessNe,
    _hwitnessWeight, hLeast⟩
  apply hLeast (horizontalAugmentation z)
  · exact ((augmentationChainMap A x).mapMiddleCycle ⟨z, hz⟩).2
  · exact horizontalAugmentation_ne_zero_of_homologyProjection_ne_zero
      A x z hz hProjected
end QEC.Coding.BalancedProduct.HorizontalSubsystem
