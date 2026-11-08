-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.augmentation_groupConj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:48:07.645193+00:00
-- url     : https://prove2.me/submissions/a77ee453-9c28-4ef5-9a79-e1418c3aceb3

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    {G : Type*} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) :
    HorizontalSubsystem.augmentation (LiftedProduct.groupConj a) =
      HorizontalSubsystem.augmentation a := by
  rw [HorizontalSubsystem.augmentation_apply,
    HorizontalSubsystem.augmentation_apply]
  change (∑ g : G, a.coeff g⁻¹) = ∑ g : G, a.coeff g
  exact Equiv.sum_comp (Equiv.inv G) a.coeff
end QEC.Coding.BalancedProduct.BE20Balanced
