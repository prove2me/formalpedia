-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.tillichZemorHypergraphProductDiagonalFullRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:47:02.005216+00:00
-- url     : https://prove2.me/submissions/4c69aacb-48c4-49e9-a808-ec73ebb5ce87

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Results_QLDPC_HypergraphProductParameters
import Theorems.Thm_QEC_Coding_HypergraphProduct_card_qubitIndex_diagonal_fullRank
import Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_diagonal_fullRank
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_middleHomology_diagonal_fullRank
import Theorems.Thm_QEC_Coding_HypergraphProduct_xCheckWeight_diagonal_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_zCheckWeight_diagonal_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Fintype.card (QubitIndex Row Col Row Col) =
      Fintype.card Col ^ 2 +
        (Fintype.card Col - Dimension (firstCode (diagonalData H))) ^ 2 ∧
    Module.finrank (ZMod 2) (chainComplex (diagonalData H)).middleHomology =
      Dimension (firstCode (diagonalData H)) ^ 2 ∧
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode (diagonalData H)).xCode
        (binaryCSSCode (diagonalData H)).zCode =
      extendedMinimumDistance (firstCode (diagonalData H)) ∧
    (∀ r c, HammingWeight
        (wordLinearMapTranspose (boundary1 (diagonalData H))
          (Pi.single (r, c) 1)) =
      rowWeight H r + columnWeight H c) ∧
    (∀ c r, HammingWeight
        (boundary2 (diagonalData H) (Pi.single (c, r) 1)) =
      rowWeight H r + columnWeight H c) := by
  exact ⟨card_qubitIndex_diagonal_fullRank H hFull,
    finrank_middleHomology_diagonal_fullRank H hFull,
    extendedAlgebraicCSSMinimumDistance_diagonal_fullRank H hFull,
    xCheckWeight_diagonal_eq H, zCheckWeight_diagonal_eq H⟩
end QEC.Coding.HypergraphProduct
