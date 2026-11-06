-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.HorizontalSubsystem.sum_leftRegularMatrix_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:33.22177+00:00
-- url     : https://prove2.me/submissions/40fb993e-bf80-4e6e-8b0f-fa768cc44fcc

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
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (i : G) :
    (∑ j : G, LiftedProduct.leftRegularMatrix a i j) = augmentation a := by
  change (∑ j : G, a.coeff (i * j⁻¹)) = augmentation a
  rw [augmentation_apply]
  exact Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft i)) a.coeff
end QEC.Coding.BalancedProduct.HorizontalSubsystem
