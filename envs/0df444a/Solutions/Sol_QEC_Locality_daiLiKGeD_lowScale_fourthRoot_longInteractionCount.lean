-- Prove2me | solution 1 for QEC.Locality.daiLiKGeD_lowScale_fourthRoot_longInteractionCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:39:16.595209+00:00
-- url     : https://prove2.me/submissions/9a3bab8e-99c4-44b0-b813-1702b2749cde

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Theorems.Thm_QEC_Locality_daiLiKGeDFourthRootThreshold_pow_four
import Theorems.Thm_QEC_Locality_one_le_daiLiKGeDFourthRootThreshold
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
import Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_card_daiLiKGeDSeparator_le_conservative
import Theorems.Thm_QEC_Locality_daiLiBadGridTotalF_le_four_mul_globalCounter
import Theorems.Thm_QEC_Locality_daiLiKGeD_encodedQubits_le_separator_card
import Theorems.Thm_QEC_Locality_exists_daiLiBadGridCellSubdivision
import Theorems.Thm_QEC_Locality_exists_good_vertex_translation

section
noncomputable section
namespace QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
private theorem daiLiKGeD_lowScale_count_of_concrete_separator
    {k d n ell w vertex longCount : ℝ}
    (hk : 0 ≤ k) (hd : 0 < d) (hn : 0 < n)
    (hkn : k ≤ n) (hLowScale : d ^ 2 ≤ k * n) (hell : 0 < ell)
    (hFourth : ell ^ 4 = k * d ^ 2 / (100 ^ 4 * n))
    (hWidth : w = d / (100 * ell))
    (hVertex : vertex ≤ (32 * ell ^ 2 / w ^ 2) * n)
    (hSeparator : k ≤ vertex + 2 * longCount + 960 * ell ^ 2 * k / d) :
    k / 100 ≤ longCount := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hell0 : ell ≠ 0 := ne_of_gt hell
  have hFourthDenom : 0 < (100 : ℝ) ^ 4 * n := by positivity
  have hFourthCleared : ell ^ 4 * (100 ^ 4 * n) = k * d ^ 2 :=
    (eq_div_iff hFourthDenom.ne').mp hFourth
  have hVertexExact : (32 * ell ^ 2 / w ^ 2) * n = (8 / 2500 : ℝ) * k := by
    rw [hWidth]
    field_simp [hd0, hell0]
    nlinarith [hFourthCleared]
  have hVertexSmall : vertex ≤ k / 100 := by
    rw [hVertexExact] at hVertex
    nlinarith
  have hFourthBound : ell ^ 4 ≤ d ^ 2 / 100 ^ 4 := by
    rw [hFourth]
    apply (div_le_iff₀ (mul_pos (by positivity : (0 : ℝ) < 100 ^ 4) hn)).2
    have hScale : 0 ≤ (n - k) * d ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hkn) (sq_nonneg d)
    have hSourceDomain : 0 ≤ k * n - d ^ 2 := sub_nonneg.mpr hLowScale
    nlinarith [hSourceDomain]
  have hSquareBound : ell ^ 2 ≤ d / 10000 := by
    by_contra h
    have hSquareLarge : d / 10000 < ell ^ 2 := lt_of_not_ge h
    have hdNonneg : 0 ≤ d := hd.le
    have hEllSqNonneg : 0 ≤ ell ^ 2 := sq_nonneg ell
    nlinarith [sq_nonneg (ell ^ 2 - d / 10000)]
  have hRectangleSmall : 960 * ell ^ 2 * k / d ≤ k / 10 := by
    apply (div_le_iff₀ hd).2
    have hScale : 0 ≤ (d / 10000 - ell ^ 2) * k :=
      mul_nonneg (sub_nonneg.mpr hSquareBound) hk
    nlinarith
  nlinarith
private theorem daiLi_encodedQubits_le_blockLength
    (P : Coding.StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : Coding.StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : Coding.StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ)
    (hScale : ell = daiLiKGeDFourthRootThreshold
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ))
    (hWidth : w = daiLiKGeDGridWidth (d : ℝ) ell)
    (hD : 0 < d) (hKGeD : d ≤ P.encodedQubits)
    (hLowScale : (d : ℝ) ≤ Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι))
    (hAboveBPT : (100 : ℝ) ^ 4 * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2)
    (hWidthNat : 1 ≤ w)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * ell)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hGoodBaseCard : ∀ (t : GridTranslation w)
      (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell)) →
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell)) →
      ∀ cell,
        Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding ell d w
          (gridOrigin w t) rectangles →
        (centeredRectangleQubits embedding
          (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBadBaseCard : ∀ (t : GridTranslation w)
      (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell)) →
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell)) →
      ∀ cell slot,
        Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding ell d w
          (gridOrigin w t) rectangles →
        (centeredRectangleQubits embedding
          (daiLiRectangleCenter
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
              (Sum.inr (cell, slot))).1
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
              (Sum.inr (cell, slot))).2)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hCellWidth : 5 * ell ≤ w) (hInternalSideScale : 12 * ell * w < d)
    (hGridWidth : 4 * ell ≤ w) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    (P.encodedQubits : ℝ) / 100 ≤ (P.longInteractionCount embedding ell : ℝ) := by
  have hKPositiveNat : 0 < P.encodedQubits := lt_of_lt_of_le hD hKGeD
  have hKLeNNat : P.encodedQubits ≤ Fintype.card ι :=
    daiLi_encodedQubits_le_blockLength P
  have hNPositiveNat : 0 < Fintype.card ι :=
    lt_of_lt_of_le hKPositiveNat hKLeNNat
  have hk : 0 ≤ (P.encodedQubits : ℝ) := Nat.cast_nonneg _
  have hd : 0 < (d : ℝ) := by exact_mod_cast hD
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hNPositiveNat
  have hkn : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast hKLeNNat
  have hProductNonneg : 0 ≤ (P.encodedQubits : ℝ) * Fintype.card ι :=
    mul_nonneg hk hn.le
  have hLowScaleSquare : (d : ℝ) ^ 2 ≤ (P.encodedQubits : ℝ) * Fintype.card ι := by
    have hRootSquare : Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι) ^ 2 =
        (P.encodedQubits : ℝ) * Fintype.card ι :=
      Real.sq_sqrt hProductNonneg
    nlinarith [sq_nonneg ((d : ℝ) -
      Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι))]
  have hEllNat : 1 ≤ ell := by
    rw [hScale]
    exact one_le_daiLiKGeDFourthRootThreshold hk hn hAboveBPT
  have hEll : 0 < ell := by linarith
  have hWidthPos : 0 < w := lt_of_lt_of_le (by norm_num) hWidthNat
  have hEdge : 1 ≤ 2 * ell := by nlinarith
  have hFourth : ell ^ 4 =
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2 /
        (100 ^ 4 * Fintype.card ι) := by
    rw [hScale]
    exact daiLiKGeDFourthRootThreshold_pow_four hk hn
  by_contra hLower
  have hLongSmall : (P.longInteractionCount embedding ell : ℝ) <
      (P.encodedQubits : ℝ) / 100 := lt_of_not_ge hLower
  have hLongSmallNat : 100 * P.longInteractionCount embedding ell < P.encodedQubits := by
    have hLongSmallReal : (100 : ℝ) * P.longInteractionCount embedding ell <
        P.encodedQubits := by
      nlinarith
    exact_mod_cast hLongSmallReal
  have hGlobal : 50 * (∑ q : ι, P.daiLiInteractionCounter embedding ell q) ≤
      P.encodedQubits := by
    rw [P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding ell]
    omega
  obtain ⟨t, hVertex⟩ := exists_good_vertex_translation w ell hEll hGridWidth embedding.point
  obtain ⟨atoms, rectangles, hAtoms, hRectangles, _hOrdered, _hPairwise, _hCover,
      _hPieces, hRectangleCount⟩ :=
    exists_daiLiBadGridCellSubdivision P embedding ell ell d w (gridOrigin w t) hEll hCellWidth
  have hOverlap := daiLiBadGridTotalF_le_four_mul_globalCounter P embedding ell d hWidthPos
    (gridOrigin w t)
  have hDimensionNat := daiLiKGeD_encodedQubits_le_separator_card P embedding d hDistance
    ell w ell t atoms rectangles hAtoms hRectangles hEllNat hWidthNat hEllNat hWidthPos hEll
    le_rfl baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
    hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
    hReachVerticalGood hReachVerticalBad
    (hGoodBaseCard t atoms rectangles hAtoms hRectangles)
    (hBadBaseCard t atoms rectangles hAtoms hRectangles)
    hBoundaryBudget hShortPackingScale hCellWidth hInternalSideScale hGridWidth hEdge hGridLong
    hGridSideSmall
  have hDimension : (P.encodedQubits : ℝ) ≤
      ((daiLiKGeDSeparator P embedding ell w ell t
        (daiLiBadGridCells P embedding ell d w (gridOrigin w t)) rectangles).card : ℝ) := by
    exact_mod_cast hDimensionNat
  have hSeparator := card_daiLiKGeDSeparator_le_conservative P embedding ell w ell t
    (daiLiBadGridCells P embedding ell d w (gridOrigin w t)) rectangles d P.encodedQubits
    hEllNat hD hRectangleCount hOverlap hGlobal
  have hCombined : (P.encodedQubits : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        2 * (P.longInteractionCount embedding ell : ℝ) +
          960 * ell ^ 2 * (P.encodedQubits : ℝ) / d := by
    rw [P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding ell] at hSeparator
    norm_num at hSeparator
    exact hDimension.trans hSeparator
  have hConclusion := daiLiKGeD_lowScale_count_of_concrete_separator hk hd hn hkn
    hLowScaleSquare hEll hFourth hWidth hVertex hCombined
  exact (not_lt_of_ge hConclusion hLongSmall)
end QEC.Locality
