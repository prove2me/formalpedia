-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.quotientBoundary_basis_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:27:29.797951+00:00
-- url     : https://prove2.me/submissions/3f66f58e-285b-4047-8a30-188314e19a85

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_constantOrbitWord
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_constantOrbitWord
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_single_le_one
import Theorems.Thm_QEC_Coding_HammingWeight_linearMap_le_of_basis


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G] [Nonempty G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (L : Nat)
    (hBasis : ∀ i : aCol × G,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ L)
    (c : aCol) :
    HammingWeight
      (HorizontalSubsystem.quotientBoundary A (Pi.single c 1)) ≤ L := by
  let z : Word (ZMod 2) aCol := Pi.single c 1
  have hLift := HammingWeight_linearMap_le_of_basis
    (PKDistance.tannerAction A) L hBasis
      (PKDistance.constantOrbitWord (G := G) z)
  rw [PKDistance.tannerAction_constantOrbitWord,
    PKDistance.HammingWeight_constantOrbitWord,
    PKDistance.HammingWeight_constantOrbitWord] at hLift
  have hz : HammingWeight z ≤ 1 := by
    exact ClassicalWeightReduction.HammingWeight_single_le_one (F := ZMod 2) c
  have hCard : 0 < Fintype.card G := Fintype.card_pos
  have hMul : Fintype.card G *
      HammingWeight (HorizontalSubsystem.quotientBoundary A z) ≤
      Fintype.card G * L := by
    calc
    Fintype.card G *
        HammingWeight (HorizontalSubsystem.quotientBoundary A z) ≤
        L * (Fintype.card G * HammingWeight z) := hLift
    _ ≤ L * (Fintype.card G * 1) :=
      Nat.mul_le_mul_left L (Nat.mul_le_mul_left _ hz)
    _ = Fintype.card G * L := by ring
  exact Nat.le_of_mul_le_mul_left hMul hCard
end QEC.Coding.BalancedProduct.BE20Balanced
