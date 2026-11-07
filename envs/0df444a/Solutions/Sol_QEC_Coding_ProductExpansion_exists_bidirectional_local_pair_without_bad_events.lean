-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_bidirectional_local_pair_without_bad_events
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:30:15.25684+00:00
-- url     : https://prove2.me/submissions/a218d360-af75-46b9-a6f3-6b7f0a164528

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badForwardRectanglePairs_mul_rankPenalty_le
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badReverseRectanglePairs_mul_rankPenalty_le
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badFirstKernelPairs_mul_penalty_le
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badFirstImagePairs_mul_penalty_le
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badSecondKernelPairs_mul_penalty_le
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badSecondImagePairs_mul_penalty_le
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badBidirectionalLocalPairs_le_add
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
namespace QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
private theorem six_mul_lt_of_scaled_bound
    (bad factor penalty total : Nat)
    (hTotalPositive : 0 < total)
    (hBound : bad * penalty ≤ factor * total)
    (hFactor : 6 * factor < penalty) :
    6 * bad < total := by
  have hScaled : (6 * bad) * penalty < total * penalty := by
    calc
      (6 * bad) * penalty = 6 * (bad * penalty) := by simp [mul_assoc]
      _ ≤ 6 * (factor * total) := Nat.mul_le_mul_left 6 hBound
      _ = (6 * factor) * total := by simp [mul_assoc]
      _ < penalty * total :=
        Nat.mul_lt_mul_of_pos_right hFactor hTotalPositive
      _ = total * penalty := Nat.mul_comm _ _
  exact Nat.lt_of_mul_lt_mul_right hScaled
end QEC.Coding.ProductExpansion
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
set_option maxHeartbeats 1200000
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (d s m k : Nat)
    (hFirstKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hFirstImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hSecondKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R')
    (hSecondImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hForwardRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R))
    (hReverseRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R')) :
    ∃ (h : Matrix R W F) (g' : Matrix R' W F),
      (∀ c : Word F W, h.mulVec c = 0 → c ≠ 0 →
        d ≤ HammingWeight c) ∧
      (∀ a : Word F R, a ≠ 0 →
        d ≤ HammingWeight (h.transpose.mulVec a)) ∧
      (∀ c : Word F W, g'.mulVec c = 0 → c ≠ 0 →
        d ≤ HammingWeight c) ∧
      (∀ a : Word F R', a ≠ 0 →
        d ≤ HammingWeight (g'.transpose.mulVec a)) ∧
      (¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (generatorImageParityCheck g' * x).rank ∧
          ProductKernel h (generatorImageParityCheck g') x) ∧
      (¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (generatorImageParityCheck h * x).rank ∧
          ProductKernel g' (generatorImageParityCheck h) x) := by
  classical
  let distanceFactor := ∑ t : Fin d,
    Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1
  let firstKernelPenalty := (Nat.card F) ^ Fintype.card R
  let firstImageFactor := (Nat.card F) ^ Fintype.card R * distanceFactor
  let imagePenalty := (Nat.card F) ^ Fintype.card W
  let secondKernelPenalty := (Nat.card F) ^ Fintype.card R'
  let secondImageFactor := (Nat.card F) ^ Fintype.card R' * distanceFactor
  let rectangleFactor :=
    (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
      (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
        (Nat.card F) ^ (2 * m * Fintype.card W + s))
  let forwardPenalty := (Nat.card F) ^ (k * Fintype.card R)
  let reversePenalty := (Nat.card F) ^ (k * Fintype.card R')
  let firstKernelBad := Nat.card (badFirstKernelPairs
    (F := F) (W := W) (R := R) (R' := R') d)
  let firstImageBad := Nat.card (badFirstImagePairs
    (F := F) (W := W) (R := R) (R' := R') d)
  let secondKernelBad := Nat.card (badSecondKernelPairs
    (F := F) (W := W) (R := R) (R' := R') d)
  let secondImageBad := Nat.card (badSecondImagePairs
    (F := F) (W := W) (R := R) (R' := R') d)
  let forwardBad := Nat.card (badForwardRectanglePairs
    (F := F) (W := W) (R := R) (R' := R') s m k)
  let reverseBad := Nat.card (badReverseRectanglePairs
    (F := F) (W := W) (R := R) (R' := R') s m k)
  let total := Nat.card (LocalMatrixPair
    (F := F) (W := W) (R := R) (R' := R'))
  have hTotalPositive : 0 < total := Nat.card_pos
  have hFirstKernelBound : firstKernelBad * firstKernelPenalty ≤
      distanceFactor * total := by
    simpa [firstKernelBad, firstKernelPenalty, distanceFactor, total] using
      card_badFirstKernelPairs_mul_penalty_le
        (F := F) (W := W) (R := R) (R' := R') d
  have hFirstImageBound : firstImageBad * imagePenalty ≤
      firstImageFactor * total := by
    simpa [firstImageBad, imagePenalty, firstImageFactor, distanceFactor,
      total] using card_badFirstImagePairs_mul_penalty_le
        (F := F) (W := W) (R := R) (R' := R') d
  have hSecondKernelBound : secondKernelBad * secondKernelPenalty ≤
      distanceFactor * total := by
    simpa [secondKernelBad, secondKernelPenalty, distanceFactor, total] using
      card_badSecondKernelPairs_mul_penalty_le
        (F := F) (W := W) (R := R) (R' := R') d
  have hSecondImageBound : secondImageBad * imagePenalty ≤
      secondImageFactor * total := by
    simpa [secondImageBad, imagePenalty, secondImageFactor, distanceFactor,
      total] using card_badSecondImagePairs_mul_penalty_le
        (F := F) (W := W) (R := R) (R' := R') d
  have hForwardBound : forwardBad * forwardPenalty ≤
      rectangleFactor * total := by
    simpa [forwardBad, forwardPenalty, rectangleFactor, total] using
      card_badForwardRectanglePairs_mul_rankPenalty_le
        (F := F) (W := W) (R := R) (R' := R') s m k
  have hReverseBound : reverseBad * reversePenalty ≤
      rectangleFactor * total := by
    simpa [reverseBad, reversePenalty, rectangleFactor, total] using
      card_badReverseRectanglePairs_mul_rankPenalty_le
        (F := F) (W := W) (R := R) (R' := R') s m k
  have hFirstKernelSix : 6 * firstKernelBad < total :=
    six_mul_lt_of_scaled_bound firstKernelBad distanceFactor
      firstKernelPenalty total hTotalPositive hFirstKernelBound
      (by simpa [distanceFactor, firstKernelPenalty] using hFirstKernelFactor)
  have hFirstImageSix : 6 * firstImageBad < total :=
    six_mul_lt_of_scaled_bound firstImageBad firstImageFactor imagePenalty
      total hTotalPositive hFirstImageBound
      (by simpa [firstImageFactor, imagePenalty, distanceFactor] using
        hFirstImageFactor)
  have hSecondKernelSix : 6 * secondKernelBad < total :=
    six_mul_lt_of_scaled_bound secondKernelBad distanceFactor
      secondKernelPenalty total hTotalPositive hSecondKernelBound
      (by simpa [distanceFactor, secondKernelPenalty] using
        hSecondKernelFactor)
  have hSecondImageSix : 6 * secondImageBad < total :=
    six_mul_lt_of_scaled_bound secondImageBad secondImageFactor imagePenalty
      total hTotalPositive hSecondImageBound
      (by simpa [secondImageFactor, imagePenalty, distanceFactor] using
        hSecondImageFactor)
  have hForwardSix : 6 * forwardBad < total :=
    six_mul_lt_of_scaled_bound forwardBad rectangleFactor forwardPenalty
      total hTotalPositive hForwardBound
      (by simpa [rectangleFactor, forwardPenalty] using
        hForwardRectangleFactor)
  have hReverseSix : 6 * reverseBad < total :=
    six_mul_lt_of_scaled_bound reverseBad rectangleFactor reversePenalty
      total hTotalPositive hReverseBound
      (by simpa [rectangleFactor, reversePenalty] using
        hReverseRectangleFactor)
  have hBadLt : Nat.card (badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) < total :=
    (card_badBidirectionalLocalPairs_le_add
      (F := F) (W := W) (R := R) (R' := R') d s m k).trans_lt (by
        dsimp only [firstKernelBad, firstImageBad, secondKernelBad,
          secondImageBad, forwardBad, reverseBad] at *
        omega)
  have hExists : ∃ p : LocalMatrixPair
      (F := F) (W := W) (R := R) (R' := R'),
      ¬((∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ p.1.mulVec c = 0) ∨
        (∃ a : Word F R,
          a ≠ 0 ∧ HammingWeight (p.1.transpose.mulVec a) < d) ∨
        (∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ p.2.mulVec c = 0) ∨
        (∃ a : Word F R',
          a ≠ 0 ∧ HammingWeight (p.2.transpose.mulVec a) < d) ∨
        (∃ A B : Finset W,
          A.card = Fintype.card W - m ∧
          B.card = Fintype.card W - m ∧
          ∃ x : Matrix W W F,
            restrictedWeight x A B < s ∧
            k ≤ (generatorImageParityCheck p.2 * x).rank ∧
            ProductKernel p.1 (generatorImageParityCheck p.2) x) ∨
        (∃ A B : Finset W,
          A.card = Fintype.card W - m ∧
          B.card = Fintype.card W - m ∧
          ∃ x : Matrix W W F,
            restrictedWeight x A B < s ∧
            k ≤ (generatorImageParityCheck p.1 * x).rank ∧
            ProductKernel p.2 (generatorImageParityCheck p.1) x)) := by
    by_contra hNo
    have hSurjective : Function.Surjective
        (Subtype.val : badBidirectionalLocalPairs
          (F := F) (W := W) (R := R) (R' := R') d s m k →
            LocalMatrixPair (F := F) (W := W) (R := R) (R' := R')) := by
      intro p
      have hBad :
          (∃ c : Word F W,
            c ≠ 0 ∧ HammingWeight c < d ∧ p.1.mulVec c = 0) ∨
          (∃ a : Word F R,
            a ≠ 0 ∧ HammingWeight (p.1.transpose.mulVec a) < d) ∨
          (∃ c : Word F W,
            c ≠ 0 ∧ HammingWeight c < d ∧ p.2.mulVec c = 0) ∨
          (∃ a : Word F R',
            a ≠ 0 ∧ HammingWeight (p.2.transpose.mulVec a) < d) ∨
          (∃ A B : Finset W,
            A.card = Fintype.card W - m ∧
            B.card = Fintype.card W - m ∧
            ∃ x : Matrix W W F,
              restrictedWeight x A B < s ∧
              k ≤ (generatorImageParityCheck p.2 * x).rank ∧
              ProductKernel p.1 (generatorImageParityCheck p.2) x) ∨
          (∃ A B : Finset W,
            A.card = Fintype.card W - m ∧
            B.card = Fintype.card W - m ∧
            ∃ x : Matrix W W F,
              restrictedWeight x A B < s ∧
              k ≤ (generatorImageParityCheck p.1 * x).rank ∧
              ProductKernel p.2 (generatorImageParityCheck p.1) x) := by
        by_contra hGood
        exact hNo ⟨p, hGood⟩
      exact ⟨⟨p, hBad⟩, rfl⟩
    have hCardLe := Nat.card_le_card_of_surjective
      (Subtype.val : badBidirectionalLocalPairs
        (F := F) (W := W) (R := R) (R' := R') d s m k →
          LocalMatrixPair (F := F) (W := W) (R := R) (R' := R'))
      hSurjective
    have hTotalLe : total ≤ Nat.card (badBidirectionalLocalPairs
        (F := F) (W := W) (R := R) (R' := R') d s m k) := by
      dsimp only [total]
      exact hCardLe
    exact (not_le_of_gt hBadLt) hTotalLe
  obtain ⟨⟨h, g'⟩, hGood⟩ := hExists
  have h₁ := (not_or.mp hGood).1
  have hRest₂ := (not_or.mp hGood).2
  have h₂ := (not_or.mp hRest₂).1
  have hRest₃ := (not_or.mp hRest₂).2
  have h₃ := (not_or.mp hRest₃).1
  have hRest₄ := (not_or.mp hRest₃).2
  have h₄ := (not_or.mp hRest₄).1
  have hRest₅ := (not_or.mp hRest₄).2
  have h₅ := (not_or.mp hRest₅).1
  have h₆ := (not_or.mp hRest₅).2
  refine ⟨h, g', ?_, ?_, ?_, ?_, h₅, h₆⟩
  · intro c hcKernel hcNonzero
    exact Nat.le_of_not_gt (fun hcWeight =>
      h₁ ⟨c, hcNonzero, hcWeight, hcKernel⟩)
  · intro a haNonzero
    exact Nat.le_of_not_gt (fun haWeight =>
      h₂ ⟨a, haNonzero, haWeight⟩)
  · intro c hcKernel hcNonzero
    exact Nat.le_of_not_gt (fun hcWeight =>
      h₃ ⟨c, hcNonzero, hcWeight, hcKernel⟩)
  · intro a haNonzero
    exact Nat.le_of_not_gt (fun haWeight =>
      h₄ ⟨a, haNonzero, haWeight⟩)
end QEC.Coding.ProductExpansion
