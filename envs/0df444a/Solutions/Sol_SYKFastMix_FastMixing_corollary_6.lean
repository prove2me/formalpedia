-- Prove2me | solution 1 for SYKFastMix.FastMixing.corollary_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:05:52.378746+00:00
-- url     : https://prove2.me/submissions/a09d10e3-1384-4a59-916f-c223d0e3ff3e

import Mathlib
import Theorems.Thm_SYKFastMix_FastMixing_lemma_5

noncomputable section
open scoped Matrix.Norms.L2Operator ComplexConjugate
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def opVec (X : Mat ι) : ι × ι → ℂ := fun p => X p.1 p.2

private lemma opVec_eq_zero_iff (X : Mat ι) : opVec X = 0 ↔ X = 0 := by
  constructor
  · intro h
    ext a b
    exact congrFun h (a, b)
  · rintro rfl
    rfl

private lemma hsInner_eq_dotProduct (X Y : Mat ι) :
    hsInner X Y = star (opVec X) ⬝ᵥ opVec Y := by
  simp only [hsInner, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diag, dotProduct, opVec, Fintype.sum_prod_type]
  change (∑ i, ∑ j, star (X j i) * Y j i) =
    ∑ i, ∑ j, star (X i j) * Y i j
  rw [Finset.sum_comm]

private lemma opVec_applySuper (T : Super ι) (X : Mat ι) :
    opVec (applySuper T X) = T *ᵥ opVec X := rfl

private lemma hsInner_adj_mul (T : Super ι) (X : Mat ι) :
    hsInner X (applySuper (Tᴴ * T) X) = hsInner (applySuper T X) (applySuper T X) := by
  rw [hsInner_eq_dotProduct, hsInner_eq_dotProduct]
  rw [opVec_applySuper, opVec_applySuper]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  rw [star_star]

private lemma qform_sum_adj_mul {I : Type} [Fintype I] (T : I → Super ι) (X : Mat ι) :
    qform (∑ i, (T i)ᴴ * T i) X = ∑ i, hsSq (applySuper (T i) X) := by
  rw [qform, hsInner_eq_dotProduct, opVec_applySuper]
  rw [show (∑ i, (T i)ᴴ * T i) *ᵥ opVec X =
      ∑ i, ((T i)ᴴ * T i) *ᵥ opVec X by
    simpa using Matrix.sum_mulVec Finset.univ (fun i ↦ (T i)ᴴ * T i) (opVec X)]
  rw [dotProduct_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsSq, ← hsInner_adj_mul]
  rw [hsInner_eq_dotProduct, opVec_applySuper]

private lemma hsSq_eq_sum_norm_sq (X : Mat ι) :
    hsSq X = ∑ p : ι × ι, ‖opVec X p‖ ^ 2 := by
  rw [hsSq, hsInner_eq_dotProduct]
  simp only [dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Complex.sq_norm]
  change (conj (opVec X p) * opVec X p).re = Complex.normSq (opVec X p)
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

private lemma hsSq_nonneg (X : Mat ι) : 0 ≤ hsSq X := by
  rw [hsSq_eq_sum_norm_sq]
  positivity

private lemma hsSq_eq_zero_iff (X : Mat ι) : hsSq X = 0 ↔ X = 0 := by
  rw [hsSq_eq_sum_norm_sq]
  constructor
  · intro h
    have hzfun : (fun p : ι × ι ↦ ‖opVec X p‖ ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _)).mp h
    have hz : ∀ p : ι × ι, ‖opVec X p‖ ^ 2 = 0 := fun p ↦ congrFun hzfun p
    ext a b
    have hab := hz (a, b)
    simp only [sq_eq_zero_iff, norm_eq_zero] at hab
    exact hab
  · rintro rfl
    simp [opVec]

private lemma applySuper_sum_adj_mul_eq_zero_iff {I : Type} [Fintype I]
    (T : I → Super ι) (X : Mat ι) :
    applySuper (∑ i, (T i)ᴴ * T i) X = 0 ↔ ∀ i, applySuper (T i) X = 0 := by
  constructor
  · intro h i
    have hq : qform (∑ i, (T i)ᴴ * T i) X = 0 := by
      simp [qform, h, hsInner]
    rw [qform_sum_adj_mul] at hq
    have hifun : (fun j ↦ hsSq (applySuper (T j) X)) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun j ↦ hsSq_nonneg _)).mp hq
    exact (hsSq_eq_zero_iff _).mp (congrFun hifun i)
  · intro h
    apply (opVec_eq_zero_iff _).mp
    rw [opVec_applySuper]
    rw [show (∑ i, (T i)ᴴ * T i) *ᵥ opVec X =
        ∑ i, ((T i)ᴴ * T i) *ᵥ opVec X by
      simpa using Matrix.sum_mulVec Finset.univ (fun i ↦ (T i)ᴴ * T i) (opVec X)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Matrix.mulVec_mulVec, ← opVec_applySuper, h i]
    change (T i)ᴴ *ᵥ (0 : ι × ι → ℂ) = 0
    exact Matrix.mulVec_zero _

private def familyVec {I : Type} (F : I → Mat ι) : EuclideanSpace ℂ (I × (ι × ι)) :=
  WithLp.toLp 2 (fun p ↦ opVec (F p.1) p.2)

private lemma familyVec_sub {I : Type} (F G : I → Mat ι) :
    familyVec (fun i ↦ F i - G i) = familyVec F - familyVec G := by
  apply PiLp.ext
  intro p
  rfl

private lemma familyVec_eq_zero_iff {I : Type} (F : I → Mat ι) :
    familyVec F = 0 ↔ ∀ i, F i = 0 := by
  constructor
  · intro h i
    ext a b
    exact congrArg (fun v : EuclideanSpace ℂ (I × (ι × ι)) ↦ v (i, (a, b))) h
  · intro h
    apply PiLp.ext
    intro p
    change opVec (F p.1) p.2 = 0
    rw [h p.1]
    rfl

private lemma familyVec_norm_sq {I : Type} [Fintype I] (F : I → Mat ι) :
    ‖familyVec F‖ ^ 2 = ∑ i, hsSq (F i) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [familyVec, hsSq_eq_sum_norm_sq]
  rw [← Finset.univ_product_univ, Finset.sum_product]

private lemma familyVec_norm {I : Type} [Fintype I] (F : I → Mat ι) :
    ‖familyVec F‖ = Real.sqrt (∑ i, hsSq (F i)) := by
  rw [← familyVec_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

end SYKFastMix.FastMixing
open SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (hβ : 0 ≤ β * Q.J ∧ β * Q.J ≤ 1/1000)
    (hM : SYKEdge.opNorm (blockM Q w (β/4)) ≤ 150 * Q.J) :
  (∀ X, (13/14 : ℝ)^2 * qform (unfilteredK Q w β) X ≤ qform (filteredK Q w β) X) ∧
  (∀ X, applySuper (filteredK Q w β) X = 0 ↔ applySuper (unfilteredK Q w β) X = 0) := by
  let C : Fin N → Mat (SiteHilbert N) → Mat (SiteHilbert N) :=
    fun i ↦ applySuper (cMap Q w β i)
  let F : Fin N → Mat (SiteHilbert N) → Mat (SiteHilbert N) :=
    fun i ↦ applySuper (cfMap Q w β i)
  have compare (X : Mat (SiteHilbert N)) :
      (13/14 : ℝ) * ‖familyVec (fun i ↦ C i X)‖ ≤
        ‖familyVec (fun i ↦ F i X)‖ := by
    have hd := lemma_5 Q w β hβ hM X
    change Real.sqrt (∑ i, hsSq (F i X - C i X)) ≤
      (1/14 : ℝ) * Real.sqrt (∑ i, hsSq (C i X)) at hd
    rw [← familyVec_norm, ← familyVec_norm] at hd
    have htri : ‖familyVec (fun i ↦ C i X)‖ ≤
        ‖familyVec (fun i ↦ F i X)‖ +
          ‖familyVec (fun i ↦ F i X - C i X)‖ := by
      rw [familyVec_sub]
      have h := norm_sub_le (familyVec (fun i ↦ F i X))
        (familyVec (fun i ↦ F i X) - familyVec (fun i ↦ C i X))
      convert h using 1 <;> abel
    linarith
  constructor
  · intro X
    have hc := compare X
    have hnonneg : 0 ≤ (13/14 : ℝ) * ‖familyVec (fun i ↦ C i X)‖ :=
      mul_nonneg (by norm_num) (norm_nonneg _)
    have hs := (sq_le_sq₀ hnonneg
      (norm_nonneg (familyVec (fun i ↦ F i X)))).mpr hc
    rw [unfilteredK, filteredK, qform_sum_adj_mul, qform_sum_adj_mul]
    rw [← familyVec_norm_sq, ← familyVec_norm_sq]
    calc
      (13 / 14 : ℝ) ^ 2 * ‖familyVec (fun i ↦ C i X)‖ ^ 2 =
          ((13 / 14 : ℝ) * ‖familyVec (fun i ↦ C i X)‖) ^ 2 := by ring
      _ ≤ ‖familyVec (fun i ↦ F i X)‖ ^ 2 := hs
  · intro X
    rw [filteredK, unfilteredK, applySuper_sum_adj_mul_eq_zero_iff,
      applySuper_sum_adj_mul_eq_zero_iff]
    constructor
    · intro hF
      have hc := compare X
      have hf0 : familyVec (fun i ↦ F i X) = 0 :=
        (familyVec_eq_zero_iff _).mpr hF
      rw [hf0, norm_zero] at hc
      have hc0 : familyVec (fun i ↦ C i X) = 0 := by
        rw [← norm_eq_zero]
        linarith [norm_nonneg (familyVec (fun i ↦ C i X))]
      exact (familyVec_eq_zero_iff _).mp hc0
    · intro hC
      have hd := lemma_5 Q w β hβ hM X
      change Real.sqrt (∑ i, hsSq (F i X - C i X)) ≤
        (1/14 : ℝ) * Real.sqrt (∑ i, hsSq (C i X)) at hd
      rw [← familyVec_norm, ← familyVec_norm] at hd
      have hc0 : familyVec (fun i ↦ C i X) = 0 :=
        (familyVec_eq_zero_iff _).mpr hC
      rw [hc0, norm_zero, mul_zero] at hd
      have hd0 : familyVec (fun i ↦ F i X - C i X) = 0 := by
        rw [← norm_eq_zero]
        exact le_antisymm hd (norm_nonneg _)
      rw [familyVec_sub, hc0, sub_zero] at hd0
      exact (familyVec_eq_zero_iff _).mp hd0
