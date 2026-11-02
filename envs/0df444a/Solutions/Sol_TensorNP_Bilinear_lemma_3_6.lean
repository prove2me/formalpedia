-- Prove2me | solution 1 for TensorNP.Bilinear.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:48:39.074397+00:00
-- url     : https://prove2.me/submissions/68ef8491-66e5-4465-9882-28a683cef02a

import Definitions.Def_TensorNP_Bilinear_Feasibility

open Finset TensorNP.Bilinear

private def asComplex {I : Type} (x : I ⊕ I → ℝ) (i : I) : ℂ :=
  ⟨x (Sum.inl i), x (Sum.inr i)⟩

private def asReal {I : Type} (x : I → ℂ) : I ⊕ I → ℝ :=
  Sum.elim (fun i ↦ (x i).re) (fun i ↦ (x i).im)

private lemma asComplex_asReal {I : Type} (x : I → ℂ) : asComplex (asReal x) = x := by
  funext i
  exact Complex.ext rfl rfl

private lemma asReal_asComplex {I : Type} (x : I ⊕ I → ℝ) : asReal (asComplex x) = x := by
  funext i
  cases i <;> rfl

private lemma real_first {I J K : Type} [Fintype J] [Fintype K]
    (A : I → J → K → ℝ) (v : J ⊕ J → ℝ) (w : K ⊕ K → ℝ) (i : I) :
    (∑ j, ∑ k, (A i j k : ℂ) * asComplex v j * asComplex w k).re =
      ∑ j, ∑ k, doubling A (Sum.inl i) j k * v j * w k := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Fintype.sum_sum_type, doubling, neg_mul, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma imag_first {I J K : Type} [Fintype J] [Fintype K]
    (A : I → J → K → ℝ) (v : J ⊕ J → ℝ) (w : K ⊕ K → ℝ) (i : I) :
    (∑ j, ∑ k, (A i j k : ℂ) * asComplex v j * asComplex w k).im =
      ∑ j, ∑ k, doubling A (Sum.inr i) j k * v j * w k := by
  simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Fintype.sum_sum_type, doubling, neg_mul, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma real_second {I J K : Type} [Fintype I] [Fintype K]
    (A : I → J → K → ℝ) (u : I ⊕ I → ℝ) (w : K ⊕ K → ℝ) (j : J) :
    (∑ i, ∑ k, (A i j k : ℂ) * starRingEnd ℂ (asComplex u i) * asComplex w k).re =
      ∑ i, ∑ k, doubling A i (Sum.inl j) k * u i * w k := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Fintype.sum_sum_type,
    doubling, neg_mul, mul_neg, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma imag_second {I J K : Type} [Fintype I] [Fintype K]
    (A : I → J → K → ℝ) (u : I ⊕ I → ℝ) (w : K ⊕ K → ℝ) (j : J) :
    (∑ i, ∑ k, (A i j k : ℂ) * starRingEnd ℂ (asComplex u i) * asComplex w k).im =
      -(∑ i, ∑ k, doubling A i (Sum.inr j) k * u i * w k) := by
  simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Fintype.sum_sum_type,
    doubling, neg_mul, mul_neg, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma real_third {I J K : Type} [Fintype I] [Fintype J]
    (A : I → J → K → ℝ) (u : I ⊕ I → ℝ) (v : J ⊕ J → ℝ) (k : K) :
    (∑ i, ∑ j, (A i j k : ℂ) * starRingEnd ℂ (asComplex u i) * asComplex v j).re =
      ∑ i, ∑ j, doubling A i j (Sum.inl k) * u i * v j := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Fintype.sum_sum_type,
    doubling, neg_mul, mul_neg, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma imag_third {I J K : Type} [Fintype I] [Fintype J]
    (A : I → J → K → ℝ) (u : I ⊕ I → ℝ) (v : J ⊕ J → ℝ) (k : K) :
    (∑ i, ∑ j, (A i j k : ℂ) * starRingEnd ℂ (asComplex u i) * asComplex v j).im =
      -(∑ i, ∑ j, doubling A i j (Sum.inr k) * u i * v j) := by
  simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Fintype.sum_sum_type,
    doubling, neg_mul, mul_neg, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma asReal_zero {I : Type} : asReal (0 : I → ℂ) = 0 := by
  funext i
  cases i <;> simp [asReal]

private lemma asComplex_zero {I : Type} : asComplex (0 : I ⊕ I → ℝ) = 0 := by
  funext i
  apply Complex.ext <;> simp [asComplex]

private lemma asReal_ne {I : Type} {x : I → ℂ} (hx : x ≠ 0) : asReal x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg asComplex h
  simpa [asComplex_asReal, asComplex_zero] using h'

private lemma asComplex_ne {I : Type} {x : I ⊕ I → ℝ} (hx : x ≠ 0) : asComplex x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg asReal h
  simpa [asReal_asComplex, asReal_zero] using h'

private lemma conj_ne {I : Type} {x : I → ℂ} (hx : x ≠ 0) :
    (fun i ↦ starRingEnd ℂ (x i)) ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := congrFun h i
  have hh := congrArg (starRingEnd ℂ) hi
  simpa using hh

theorem solution {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) :
    TBF (doubling A) ↔ TBF (fun i j k ↦ (A i j k : ℂ)) := by
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, h1, h2, h3⟩
    refine ⟨(fun i ↦ starRingEnd ℂ (asComplex u i)), asComplex v, asComplex w,
      conj_ne (asComplex_ne hu), asComplex_ne hv, asComplex_ne hw, ?_, ?_, ?_⟩
    · intro i
      apply Complex.ext
      · rw [real_first, h1]
        rfl
      · rw [imag_first, h1]
        rfl
    · intro j
      apply Complex.ext
      · rw [real_second, h2]
        rfl
      · rw [imag_second, h2]
        simp
    · intro k
      apply Complex.ext
      · rw [real_third, h3]
        rfl
      · rw [imag_third, h3]
        simp
  · rintro ⟨u, v, w, hu, hv, hw, h1, h2, h3⟩
    let ur := asReal (fun i ↦ starRingEnd ℂ (u i))
    let vr := asReal v
    let wr := asReal w
    have hu' : (fun i ↦ starRingEnd ℂ (asComplex ur i)) = u := by
      funext i
      simp [ur, asComplex_asReal]
    have hv' : asComplex vr = v := asComplex_asReal v
    have hw' : asComplex wr = w := asComplex_asReal w
    refine ⟨ur, vr, wr, asReal_ne (conj_ne hu), asReal_ne hv, asReal_ne hw, ?_, ?_, ?_⟩
    · intro i
      cases i with
      | inl i =>
        have hh := congrArg Complex.re (h1 i)
        rw [← hv', ← hw', real_first] at hh
        simpa using hh
      | inr i =>
        have hh := congrArg Complex.im (h1 i)
        rw [← hv', ← hw', imag_first] at hh
        simpa using hh
    · intro j
      cases j with
      | inl j =>
        have hh := congrArg Complex.re (h2 j)
        rw [← hu', ← hw', real_second] at hh
        simpa using hh
      | inr j =>
        have hh := congrArg Complex.im (h2 j)
        rw [← hu', ← hw', imag_second] at hh
        exact neg_eq_zero.mp (by simpa only [Complex.zero_im] using hh)
    · intro k
      cases k with
      | inl k =>
        have hh := congrArg Complex.re (h3 k)
        rw [← hu', ← hv', real_third] at hh
        simpa using hh
      | inr k =>
        have hh := congrArg Complex.im (h3 k)
        rw [← hu', ← hv', imag_third] at hh
        exact neg_eq_zero.mp (by simpa only [Complex.zero_im] using hh)
