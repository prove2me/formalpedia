-- Prove2me | solution 1 for Verlinde2016.hessian_sq_integral_eq_laplacian_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:59:31.523978+00:00
-- url     : https://prove2.me/submissions/801216b5-3831-47c9-a71c-87ad87c543ce

import Mathlib
import Definitions.Def_Verlinde2016_Defs

set_option autoImplicit false

open Real

namespace V579

open MeasureTheory

lemma pd_contDiff {n : ℕ} (i : Fin n) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (Verlinde2016.partialDeriv i f) := by
  unfold Verlinde2016.partialDeriv
  exact (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

lemma pd_supp {n : ℕ} (i : Fin n) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (Verlinde2016.partialDeriv i f) := by
  unfold Verlinde2016.partialDeriv
  exact hf.fderiv_apply ℝ _

lemma pd_symm {n : ℕ} (i j : Fin n) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv j f)
      = Verlinde2016.partialDeriv j (Verlinde2016.partialDeriv i f) := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.1 hf).2.differentiable (by simp)
  have key : ∀ (a b : Fin n) (x : EuclideanSpace ℝ (Fin n)),
      Verlinde2016.partialDeriv a (Verlinde2016.partialDeriv b f) x
        = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b x
    unfold Verlinde2016.partialDeriv
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  funext x
  rw [key, key]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2:ℕ∞) ≤ ⊤))) _ _

lemma ibp {n : ℕ} (i : Fin n) {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfs : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (_hgs : HasCompactSupport g) :
    ∫ x, f x * Verlinde2016.partialDeriv i g x
      = - ∫ x, Verlinde2016.partialDeriv i f x * g x := by
  have hf1 := pd_contDiff i hf
  have hg1 := pd_contDiff i hg
  have hfs1 := pd_supp i hfs
  unfold Verlinde2016.partialDeriv at *
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hf1.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfs1.mul_right
  · exact (hf.continuous.mul hg1.continuous).integrable_of_hasCompactSupport hfs.mul_right
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfs.mul_right
  · intro x _; exact hf.differentiable (by simp) x
  · intro x _; exact hg.differentiable (by simp) x

lemma integrable_of {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfs : HasCompactSupport f) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Continuous g) : Integrable (fun x => f x * g x) :=
  (hf.continuous.mul hg).integrable_of_hasCompactSupport hfs.mul_right

lemma term {n : ℕ} (i j : Fin n) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hs : HasCompactSupport χ) :
    ∫ x, Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv j χ) x ^ 2
      = ∫ x, Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv i χ) x *
          Verlinde2016.partialDeriv j (Verlinde2016.partialDeriv j χ) x := by
  have c1 : ∀ (k : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) (Verlinde2016.partialDeriv k f) :=
    fun k f h => pd_contDiff k h
  have s1 : ∀ (k : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ), HasCompactSupport f →
      HasCompactSupport (Verlinde2016.partialDeriv k f) := fun k f h => pd_supp k h
  have h1 : ∫ x, Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv j χ) x ^ 2
      = ∫ x, Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv j χ) x *
          Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv j χ) x := by
    congr 1; funext x; ring
  rw [h1, ibp i (c1 _ _ (c1 _ _ hχ)) (s1 _ _ (s1 _ _ hs)) (c1 _ _ hχ) (s1 _ _ hs)]
  -- D i (D i (D j χ)) = D j (D i (D i χ))
  have e1 : Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv j χ))
      = Verlinde2016.partialDeriv j (Verlinde2016.partialDeriv i (Verlinde2016.partialDeriv i χ)) := by
    rw [pd_symm i j hχ, pd_symm i j (c1 _ _ hχ)]
  rw [e1, ← ibp j (c1 _ _ (c1 _ _ hχ)) (s1 _ _ (s1 _ _ hs)) (c1 _ _ hχ) (s1 _ _ hs)]

end V579

open Verlinde2016 in
theorem solution {n : ℕ} (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_supp : HasCompactSupport χ) :
    ∑ i, ∑ j, ∫ x, partialDeriv i (partialDeriv j χ) x ^ 2
      = ∫ x, (∑ i, partialDeriv i (partialDeriv i χ) x) ^ 2 := by
  have c2 : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (partialDeriv k (partialDeriv k χ)) :=
    fun k => V579.pd_contDiff k (V579.pd_contDiff k hχ)
  have s2 : ∀ k, HasCompactSupport (partialDeriv k (partialDeriv k χ)) :=
    fun k => V579.pd_supp k (V579.pd_supp k hχ_supp)
  simp_rw [V579.term _ _ χ hχ hχ_supp]
  have hsq : ∀ x, (∑ i, partialDeriv i (partialDeriv i χ) x) ^ 2
      = ∑ i, ∑ j, partialDeriv i (partialDeriv i χ) x * partialDeriv j (partialDeriv j χ) x := by
    intro x; rw [sq, Finset.sum_mul_sum]
  simp_rw [hsq]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_finsetSum]
    intro j _
    exact V579.integrable_of (c2 i) (s2 i) _ (c2 j).continuous
  · intro i _
    exact MeasureTheory.integrable_finsetSum _
      (fun j _ => V579.integrable_of (c2 i) (s2 i) _ (c2 j).continuous)
