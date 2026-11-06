-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalAugmentation_eq_zero_of_homologyProjection_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:35.041583+00:00
-- url     : https://prove2.me/submissions/3217f456-840c-43fa-8d11-1049d46af874

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
          ⟨z, hz⟩) = 0) :
    horizontalAugmentation z = 0 := by
  rw [horizontalHomologyProjection,
    ThreeTermChainMap.inducedMiddleHomology_mk] at hProjected
  have hInCycles := (Submodule.Quotient.mk_eq_zero
    (quotientTannerComplex A).middleBoundaryInCycles).1 hProjected
  have hBoundary : horizontalAugmentation z ∈
      (quotientTannerComplex A).middleBoundaryCode.carrier := hInCycles
  rcases ((quotientTannerComplex A).mem_middleBoundaryCode_iff
    (horizontalAugmentation z)).1 hBoundary with ⟨emptyWord, hempty⟩
  have hemptyZero : emptyWord = 0 := Subsingleton.elim _ _
  rw [hemptyZero, map_zero] at hempty
  exact hempty.symm
end QEC.Coding.BalancedProduct.HorizontalSubsystem
