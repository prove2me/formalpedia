-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.tillichZemorHypergraphProductParameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:47:00.492755+00:00
-- url     : https://prove2.me/submissions/4dfe78c2-b80f-4e7c-91c2-da74d59a80ef

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Results_QLDPC_HypergraphProductParameters
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_stabilizer_isSourceValidBinary
import Theorems.Thm_QEC_Coding_HypergraphProduct_card_qubitIndex
import Theorems.Thm_QEC_Coding_HypergraphProduct_checkWeight_le_two_mul
import Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_middleHomology_eq_dimension_products
import Theorems.Thm_QEC_Coding_HypergraphProduct_inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance
import Theorems.Thm_QEC_Coding_HypergraphProduct_qubitDegree_inl_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_qubitDegree_inr_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_qubitDegree_le_two_mul
import Theorems.Thm_QEC_Coding_HypergraphProduct_xCheckWeight_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_zCheckWeight_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary ∧
    Fintype.card (QubitIndex rowOne colOne rowTwo colTwo) =
      Fintype.card colOne * Fintype.card colTwo +
        Fintype.card rowOne * Fintype.card rowTwo ∧
    Module.finrank (ZMod 2) (chainComplex D).middleHomology =
      Dimension (firstCode D) * Dimension (secondCode D) +
        Dimension (firstTransposeCode D) *
          Dimension (secondTransposeCode D) ∧
    inputDistanceMinimum D ≤
      extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ∧
    (DistanceEqualityCondition D →
      extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode D).xCode (binaryCSSCode D).zCode =
        inputDistanceMinimum D) ∧
    (∀ r₁ c₂, HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single (r₁, c₂) 1)) =
      rowWeight D.first r₁ + columnWeight D.second c₂) ∧
    (∀ c₁ r₂, HammingWeight (boundary2 D (Pi.single (c₁, r₂) 1)) =
      rowWeight D.second r₂ + columnWeight D.first c₁) ∧
    (∀ c₁ c₂, qubitDegree D (Sum.inl (c₁, c₂)) =
      columnWeight D.first c₁ + columnWeight D.second c₂) ∧
    (∀ r₁ r₂, qubitDegree D (Sum.inr (r₁, r₂)) =
      rowWeight D.second r₂ + rowWeight D.first r₁) ∧
    (∀ w,
      (∀ r, rowWeight D.first r ≤ w) →
      (∀ c, columnWeight D.first c ≤ w) →
      (∀ r, rowWeight D.second r ≤ w) →
      (∀ c, columnWeight D.second c ≤ w) →
      ((∀ x₀, HammingWeight
          (wordLinearMapTranspose (boundary1 D) (Pi.single x₀ 1)) ≤ 2 * w) ∧
       (∀ x₂, HammingWeight (boundary2 D (Pi.single x₂ 1)) ≤ 2 * w) ∧
       (∀ q, qubitDegree D q ≤ 2 * w))) := by
  refine ⟨binaryCSSCode_stabilizer_isSourceValidBinary D,
    card_qubitIndex, finrank_middleHomology_eq_dimension_products D,
    inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance D,
    extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum D,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun r₁ c₂ => xCheckWeight_eq D r₁ c₂
  · exact fun c₁ r₂ => zCheckWeight_eq D c₁ r₂
  · exact fun c₁ c₂ => qubitDegree_inl_eq D c₁ c₂
  · exact fun r₁ r₂ => qubitDegree_inr_eq D r₁ r₂
  · intro w hRowOne hColOne hRowTwo hColTwo
    rcases checkWeight_le_two_mul D w
      hRowOne hColOne hRowTwo hColTwo with ⟨hX, hZ⟩
    exact ⟨hX, hZ,
      qubitDegree_le_two_mul D w hRowOne hColOne hRowTwo hColTwo⟩
end QEC.Coding.HypergraphProduct
