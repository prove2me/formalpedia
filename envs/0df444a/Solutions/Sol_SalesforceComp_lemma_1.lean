-- Prove2me | solution 1 for SalesforceComp.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:46:22.02156+00:00
-- url     : https://prove2.me/submissions/3fd6e91d-86ae-4c49-a7dc-4e7b134e40d7

import Mathlib
import Definitions.Def_SalesforceComp_Model

set_option autoImplicit false

open MeasureTheory SalesforceComp

namespace SalesforceComp.Lemma1Proof

theorem pd1_eq_fderiv {g : ℝ → ℝ → ℝ}
    (hg : Differentiable ℝ (fun p : ℝ × ℝ => g p.1 p.2)) (r θ : ℝ) :
    pd1 g r θ = fderiv ℝ (fun p : ℝ × ℝ => g p.1 p.2) (r, θ) (1, 0) := by
  unfold pd1
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => g p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => g p.1 p.2) (r, θ)) (r, θ) :=
    (hg (r, θ)).hasFDerivAt
  have h2 : HasDerivAt (fun r' : ℝ => (r', θ)) (1, 0) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
  exact (h1.comp_hasDerivAt r h2).deriv

theorem pd2_eq_fderiv {g : ℝ → ℝ → ℝ}
    (hg : Differentiable ℝ (fun p : ℝ × ℝ => g p.1 p.2)) (r θ : ℝ) :
    pd2 g r θ = fderiv ℝ (fun p : ℝ × ℝ => g p.1 p.2) (r, θ) (0, 1) := by
  unfold pd2
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => g p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => g p.1 p.2) (r, θ)) (r, θ) :=
    (hg (r, θ)).hasFDerivAt
  have h2 : HasDerivAt (fun θ' : ℝ => (r, θ')) (0, 1) θ :=
    (hasDerivAt_const θ r).prodMk (hasDerivAt_id θ)
  exact (h1.comp_hasDerivAt θ h2).deriv

theorem contDiff_pd1 {n : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun p : ℝ × ℝ => g p.1 p.2)) :
    ContDiff ℝ n (fun p : ℝ × ℝ => pd1 g p.1 p.2) := by
  obtain ⟨hdiff, -, hfderiv⟩ := contDiff_succ_iff_fderiv.mp hg
  have heq : (fun p : ℝ × ℝ => pd1 g p.1 p.2) =
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))) ∘
        fderiv ℝ (fun p : ℝ × ℝ => g p.1 p.2) := by
    ext ⟨r, θ⟩
    exact pd1_eq_fderiv hdiff r θ
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).contDiff.comp hfderiv

theorem contDiff_pd2 {n : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun p : ℝ × ℝ => g p.1 p.2)) :
    ContDiff ℝ n (fun p : ℝ × ℝ => pd2 g p.1 p.2) := by
  obtain ⟨hdiff, -, hfderiv⟩ := contDiff_succ_iff_fderiv.mp hg
  have heq : (fun p : ℝ × ℝ => pd2 g p.1 p.2) =
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))) ∘
        fderiv ℝ (fun p : ℝ × ℝ => g p.1 p.2) := by
    ext ⟨r, θ⟩
    exact pd2_eq_fderiv hdiff r θ
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).contDiff.comp hfderiv

theorem hasDerivAt_slice1 {g : ℝ → ℝ → ℝ}
    (hg : ContDiff ℝ 1 (fun p : ℝ × ℝ => g p.1 p.2)) (r θ : ℝ) :
    HasDerivAt (fun r' => g r' θ) (pd1 g r θ) r := by
  have hd : DifferentiableAt ℝ (fun r' => g r' θ) r :=
    ((hg.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero) r
  exact hd.hasDerivAt

theorem hasDerivAt_slice2 {g : ℝ → ℝ → ℝ}
    (hg : ContDiff ℝ 1 (fun p : ℝ × ℝ => g p.1 p.2)) (r θ : ℝ) :
    HasDerivAt (fun θ' => g r θ') (pd2 g r θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' => g r θ') θ :=
    ((hg.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero) θ
  exact hd.hasDerivAt

end SalesforceComp.Lemma1Proof

open SalesforceComp.Lemma1Proof in
theorem solution (M : Model) (r θ : ℝ) (hr : 0 ≤ r) (hθ : θ ∈ M.I) :
    0 < pd1 M.K r θ ∧ pd2 M.K r θ < 0 ∧ 0 < pd1 (pd1 M.K) r θ ∧ pd2 (pd1 M.K) r θ < 0 ∧
      pd2 (pd1 (pd1 M.K)) r θ ≤ 0 ∧ 0 ≤ pd2 (pd2 (pd1 M.K)) r θ := by
  have hC0 : Differentiable ℝ M.C := M.C_contDiff.differentiable (by norm_num)
  have hC1 : Differentiable ℝ (deriv M.C) := by
    have h := M.C_contDiff.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at h
  have hC2 : Differentiable ℝ (deriv (deriv M.C)) := by
    have h := M.C_contDiff.differentiable_iteratedDeriv 2 (by norm_num)
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at h
  have hE_cd3 : ContDiff ℝ (((2 : ℕ) : WithTop ℕ∞) + 1) (fun p : ℝ × ℝ => M.E p.1 p.2) := by
    convert M.E_contDiff using 1; norm_num
  have hE1_cd2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => pd1 M.E p.1 p.2) := contDiff_pd1 hE_cd3
  have hE2_cd2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => pd2 M.E p.1 p.2) := contDiff_pd2 hE_cd3
  have hE1_cd2' : ContDiff ℝ (((1 : ℕ) : WithTop ℕ∞) + 1) (fun p : ℝ × ℝ => pd1 M.E p.1 p.2) := by
    convert hE1_cd2 using 1; norm_num
  have hE2_cd2' : ContDiff ℝ (((1 : ℕ) : WithTop ℕ∞) + 1) (fun p : ℝ × ℝ => pd2 M.E p.1 p.2) := by
    convert hE2_cd2 using 1; norm_num
  have hE11_cd1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => pd1 (pd1 M.E) p.1 p.2) := contDiff_pd1 hE1_cd2'
  have hE12_cd1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => pd2 (pd1 M.E) p.1 p.2) := contDiff_pd2 hE1_cd2'
  have hE_cd1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => M.E p.1 p.2) := M.E_contDiff.of_le (by norm_num)
  have hE1_cd1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => pd1 M.E p.1 p.2) := hE1_cd2.of_le (by norm_num)
  have hE2_cd1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => pd2 M.E p.1 p.2) := hE2_cd2.of_le (by norm_num)
  have hK1_all : ∀ x y : ℝ, pd1 M.K x y = deriv M.C (M.E x y) * pd1 M.E x y := by
    intro x y
    unfold pd1 Model.K
    exact (((hC0 (M.E x y)).hasDerivAt).comp x (hasDerivAt_slice1 hE_cd1 x y)).deriv
  have hK2_all : ∀ x y : ℝ, pd2 M.K x y = deriv M.C (M.E x y) * pd2 M.E x y := by
    intro x y
    unfold pd2 Model.K
    exact (((hC0 (M.E x y)).hasDerivAt).comp y (hasDerivAt_slice2 hE_cd1 x y)).deriv
  have hK11_all : ∀ x y : ℝ, pd1 (pd1 M.K) x y =
      (deriv (deriv M.C) (M.E x y) * pd1 M.E x y) * pd1 M.E x y +
        deriv M.C (M.E x y) * pd1 (pd1 M.E) x y := by
    intro x y
    unfold pd1
    have hfun : (fun x' => deriv (fun r' => M.K r' y) x') =
        fun x' => deriv M.C (M.E x' y) * pd1 M.E x' y := by
      ext x'; exact hK1_all x' y
    rw [hfun]
    let hd1 := HasDerivAt.comp x (hC1 (M.E x y)).hasDerivAt (hasDerivAt_slice1 hE_cd1 x y)
    have hd2 : HasDerivAt (fun x' => pd1 M.E x' y) (pd1 (pd1 M.E) x y) x :=
      hasDerivAt_slice1 hE1_cd1 x y
    exact (hd1.mul hd2).deriv
  have hK12_all : ∀ x y : ℝ, pd2 (pd1 M.K) x y =
      (deriv (deriv M.C) (M.E x y) * pd2 M.E x y) * pd1 M.E x y +
        deriv M.C (M.E x y) * pd2 (pd1 M.E) x y := by
    intro x y
    unfold pd2
    have hfun : (fun y' => pd1 M.K x y') =
        fun y' => deriv M.C (M.E x y') * pd1 M.E x y' := by
      ext y'; exact hK1_all x y'
    rw [hfun]
    let hd1 := HasDerivAt.comp y (hC1 (M.E x y)).hasDerivAt (hasDerivAt_slice2 hE_cd1 x y)
    have hd2 : HasDerivAt (fun y' => pd1 M.E x y') (pd2 (pd1 M.E) x y) y :=
      hasDerivAt_slice2 hE1_cd1 x y
    exact (hd1.mul hd2).deriv
  have hK112 : pd2 (pd1 (pd1 M.K)) r θ =
      ((deriv (deriv (deriv M.C)) (M.E r θ) * pd2 M.E r θ) * pd1 M.E r θ +
          deriv (deriv M.C) (M.E r θ) * pd2 (pd1 M.E) r θ) * pd1 M.E r θ +
        (deriv (deriv M.C) (M.E r θ) * pd1 M.E r θ) * pd2 (pd1 M.E) r θ +
      ((deriv (deriv M.C) (M.E r θ) * pd2 M.E r θ) * pd1 (pd1 M.E) r θ +
        deriv M.C (M.E r θ) * pd2 (pd1 (pd1 M.E)) r θ) := by
    unfold pd2
    have hfun : (fun y' => pd1 (pd1 M.K) r y') =
        fun y' => ((deriv (deriv M.C) (M.E r y') * pd1 M.E r y') * pd1 M.E r y') +
          (deriv M.C (M.E r y') * pd1 (pd1 M.E) r y') := by
      ext y'; exact hK11_all r y'
    rw [hfun]
    let hdC2 := HasDerivAt.comp θ (hC2 (M.E r θ)).hasDerivAt (hasDerivAt_slice2 hE_cd1 r θ)
    let hdC1 := HasDerivAt.comp θ (hC1 (M.E r θ)).hasDerivAt (hasDerivAt_slice2 hE_cd1 r θ)
    have hdE1 : HasDerivAt (fun y' => pd1 M.E r y') (pd2 (pd1 M.E) r θ) θ :=
      hasDerivAt_slice2 hE1_cd1 r θ
    have hdE11 : HasDerivAt (fun y' => pd1 (pd1 M.E) r y') (pd2 (pd1 (pd1 M.E)) r θ) θ :=
      hasDerivAt_slice2 hE11_cd1 r θ
    exact (((hdC2.mul hdE1).mul hdE1).add (hdC1.mul hdE11)).deriv
  have hK122 : pd2 (pd2 (pd1 M.K)) r θ =
      ((deriv (deriv (deriv M.C)) (M.E r θ) * pd2 M.E r θ) * pd2 M.E r θ +
          deriv (deriv M.C) (M.E r θ) * pd2 (pd2 M.E) r θ) * pd1 M.E r θ +
        (deriv (deriv M.C) (M.E r θ) * pd2 M.E r θ) * pd2 (pd1 M.E) r θ +
      ((deriv (deriv M.C) (M.E r θ) * pd2 M.E r θ) * pd2 (pd1 M.E) r θ +
        deriv M.C (M.E r θ) * pd2 (pd2 (pd1 M.E)) r θ) := by
    unfold pd2
    have hfun : (fun y' => deriv (fun θ' => pd1 M.K r θ') y') =
        fun y' => ((deriv (deriv M.C) (M.E r y') * pd2 M.E r y') * pd1 M.E r y') +
          (deriv M.C (M.E r y') * pd2 (pd1 M.E) r y') := by
      ext y'; exact hK12_all r y'
    rw [hfun]
    let hdC2 := HasDerivAt.comp θ (hC2 (M.E r θ)).hasDerivAt (hasDerivAt_slice2 hE_cd1 r θ)
    let hdC1 := HasDerivAt.comp θ (hC1 (M.E r θ)).hasDerivAt (hasDerivAt_slice2 hE_cd1 r θ)
    have hdE2 : HasDerivAt (fun y' => pd2 M.E r y') (pd2 (pd2 M.E) r θ) θ :=
      hasDerivAt_slice2 hE2_cd1 r θ
    have hdE1 : HasDerivAt (fun y' => pd1 M.E r y') (pd2 (pd1 M.E) r θ) θ :=
      hasDerivAt_slice2 hE1_cd1 r θ
    have hdE12 : HasDerivAt (fun y' => pd2 (pd1 M.E) r y') (pd2 (pd2 (pd1 M.E)) r θ) θ :=
      hasDerivAt_slice2 hE12_cd1 r θ
    exact (((hdC2.mul hdE2).mul hdE1).add (hdC1.mul hdE12)).deriv
  have sC1 : 0 < deriv M.C (M.E r θ) := M.C1_pos r θ hr hθ
  have sC11 : 0 < deriv (deriv M.C) (M.E r θ) := M.C11_pos r θ hr hθ
  have sC111 : 0 ≤ deriv (deriv (deriv M.C)) (M.E r θ) := M.C111_nonneg r θ hr hθ
  have sE1 : 0 < pd1 M.E r θ := M.E1_pos r θ hr hθ
  have sE2 : pd2 M.E r θ < 0 := M.E2_neg r θ hr hθ
  have sE11 : 0 ≤ pd1 (pd1 M.E) r θ := M.E11_nonneg r θ hr hθ
  have sE12 : pd2 (pd1 M.E) r θ ≤ 0 := M.E12_nonpos r θ hr hθ
  have sE22 : 0 ≤ pd2 (pd2 M.E) r θ := M.E22_nonneg r θ hr hθ
  have sE112 : pd2 (pd1 (pd1 M.E)) r θ ≤ 0 := M.E112_nonpos r θ hr hθ
  have sE122 : 0 ≤ pd2 (pd2 (pd1 M.E)) r θ := M.E122_nonneg r θ hr hθ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK1_all]
    exact mul_pos sC1 sE1
  · rw [hK2_all]
    exact mul_neg_of_pos_of_neg sC1 sE2
  · rw [hK11_all]
    have t1 : 0 < (deriv (deriv M.C) (M.E r θ) * pd1 M.E r θ) * pd1 M.E r θ :=
      mul_pos (mul_pos sC11 sE1) sE1
    have t2 : 0 ≤ deriv M.C (M.E r θ) * pd1 (pd1 M.E) r θ := mul_nonneg sC1.le sE11
    linarith
  · rw [hK12_all]
    have t1 : (deriv (deriv M.C) (M.E r θ) * pd2 M.E r θ) * pd1 M.E r θ < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg sC11 sE2) sE1
    have t2 : deriv M.C (M.E r θ) * pd2 (pd1 M.E) r θ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos sC1.le sE12
    linarith
  · rw [hK112]
    have t1 : (deriv (deriv (deriv M.C)) (M.E r θ) * pd2 M.E r θ) * pd1 M.E r θ * pd1 M.E r θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos sC111 sE2.le) sE1.le)
        sE1.le
    have t2 : deriv (deriv M.C) (M.E r θ) * pd2 (pd1 M.E) r θ * pd1 M.E r θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos sC11.le sE12) sE1.le
    have t3 : (deriv (deriv M.C) (M.E r θ) * pd2 M.E r θ) * pd1 (pd1 M.E) r θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_neg_of_pos_of_neg sC11 sE2).le sE11
    have t4 : deriv M.C (M.E r θ) * pd2 (pd1 (pd1 M.E)) r θ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos sC1.le sE112
    linarith
  · rw [hK122]
    have t1 : 0 ≤ (deriv (deriv (deriv M.C)) (M.E r θ) * pd2 M.E r θ) * pd2 M.E r θ * pd1 M.E r θ :=
      mul_nonneg
        (mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos sC111 sE2.le) sE2.le)
        sE1.le
    have t2 : 0 ≤ deriv (deriv M.C) (M.E r θ) * pd2 (pd2 M.E) r θ * pd1 M.E r θ :=
      mul_nonneg (mul_nonneg sC11.le sE22) sE1.le
    have t3 : 0 ≤ (deriv (deriv M.C) (M.E r θ) * pd2 M.E r θ) * pd2 (pd1 M.E) r θ :=
      mul_nonneg_of_nonpos_of_nonpos (mul_neg_of_pos_of_neg sC11 sE2).le sE12
    have t4 : 0 ≤ deriv M.C (M.E r θ) * pd2 (pd2 (pd1 M.E)) r θ :=
      mul_nonneg sC1.le sE122
    linarith
