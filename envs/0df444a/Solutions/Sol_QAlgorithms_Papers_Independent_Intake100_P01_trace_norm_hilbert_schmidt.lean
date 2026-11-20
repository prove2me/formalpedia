-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P01.trace_norm_hilbert_schmidt
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T03:07:15.103896+00:00
-- url     : https://prove2.me/submissions/d2e4581a-bad3-4dca-a5a8-31eb794f0562

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.20, Lemma 13, (A1): arbitrary finite complex operator.
Printed: support described by nonzero eigenvalues. Changed: rank(X), the
support dimension of |X|. Why: the proof uses singular values and the
printed gloss fails for nonzero nilpotents. No Hermiticity is added. -/
theorem _root_.solution {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) :
    traceNorm X ^ 2 ≤ (Matrix.rank X : ℝ) * frobNorm X ^ 2 := by
  classical
  set A : Matrix I I ℂ := Xᴴ * X with hAdef
  have hA : A.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self X
  set e := hA.eigenvalues with he
  have he0 : ∀ i, 0 ≤ e i := fun i => Matrix.eigenvalues_conjTranspose_mul_self_nonneg X i
  -- trace norm as sum of square roots
  have htr : traceNorm X = ∑ i, Real.sqrt (e i) := by
    unfold traceNorm
    rw [← hAdef, hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
    simp [he, Complex.re_sum]
  -- frobenius norm squared as sum of eigenvalues
  have hfr : frobNorm X ^ 2 = ∑ i, e i := by
    have h1 : frobNorm X ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
      unfold frobNorm
      rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have h2 : (A.trace).re = ∑ i, e i := by
      rw [hA.trace_eq_sum_eigenvalues]; simp [he, Complex.re_sum]
    rw [h1, ← h2, hAdef, Matrix.trace, Complex.re_sum]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  have hrk : (Matrix.rank X : ℝ) = ((Finset.univ.filter fun i => e i ≠ 0).card : ℝ) := by
    have hr : (Xᴴ * X).rank = X.rank := by
      open scoped ComplexOrder in exact Matrix.rank_conjTranspose_mul_self X
    rw [← hr, ← hAdef, hA.rank_eq_card_non_zero_eigs,
      Fintype.card_subtype]
  rw [htr, hfr, hrk]
  set S := Finset.univ.filter fun i => e i ≠ 0
  have hs1 : ∑ i, Real.sqrt (e i) = ∑ i ∈ S, Real.sqrt (e i) := by
    rw [Finset.sum_filter_of_ne]; intro i _ h h0; apply h; simp [h0]
  have hs2 : ∑ i ∈ S, Real.sqrt (e i) ^ 2 ≤ ∑ i, e i := by
    calc ∑ i ∈ S, Real.sqrt (e i) ^ 2 = ∑ i ∈ S, e i :=
          Finset.sum_congr rfl fun i _ => Real.sq_sqrt (he0 i)
      _ ≤ ∑ i, e i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => he0 i)
  rw [hs1]
  calc (∑ i ∈ S, Real.sqrt (e i)) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, Real.sqrt (e i) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (S.card : ℝ) * ∑ i, e i := mul_le_mul_of_nonneg_left hs2 (Nat.cast_nonneg _)

end QAlgorithms.Papers.Independent.Intake100.P01

end

