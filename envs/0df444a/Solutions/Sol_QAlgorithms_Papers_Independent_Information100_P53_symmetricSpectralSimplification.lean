-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.symmetricSpectralSimplification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:23:37.061684+00:00
-- url     : https://prove2.me/submissions/d7b165f7-f51e-4225-99a5-f316c20b04b5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P53 in
lemma g53h_top_sum {α : Type*} [DecidableEq α] (w : α → ℝ) (k : ℕ) (I J : Finset α)
    (hI : IsTopSelection k w I) (hJ : IsTopSelection k w J) :
    ∑ z ∈ I, w z = ∑ z ∈ J, w z := by
  have e1 := Finset.sum_sdiff (f := w) (Finset.inter_subset_left : I ∩ J ⊆ I)
  have e2 := Finset.sum_sdiff (f := w) (Finset.inter_subset_right : I ∩ J ⊆ J)
  rw [Finset.sdiff_inter_self_left] at e1
  rw [Finset.sdiff_inter_self_right] at e2
  have hc1 := Finset.card_sdiff_add_card_inter I J
  have hc2 := Finset.card_sdiff_add_card_inter J I
  rw [Finset.inter_comm J I] at hc2
  have hcard : (I \ J).card = (J \ I).card := by rw [hI.1] at hc1; rw [hJ.1] at hc2; omega
  have hsd : ∑ z ∈ I \ J, w z = ∑ z ∈ J \ I, w z := by
    rcases (J \ I).eq_empty_or_nonempty with h | ⟨v0, hv0⟩
    · rw [h, Finset.card_empty, Finset.card_eq_zero] at hcard
      rw [h, hcard]
    · have hv0' := Finset.mem_sdiff.1 hv0
      have hc : ∀ u ∈ I \ J, ∀ v ∈ J \ I, w u = w v := by
        intro u hu v hv
        have hu' := Finset.mem_sdiff.1 hu; have hv' := Finset.mem_sdiff.1 hv
        exact le_antisymm (hJ.2 v hv'.1 u hu'.2) (hI.2 u hu'.1 v hv'.2)
      rcases (I \ J).eq_empty_or_nonempty with h2 | ⟨u0, hu0⟩
      · rw [h2, Finset.card_empty] at hcard
        exact absurd (Finset.card_eq_zero.1 hcard.symm) (Finset.nonempty_iff_ne_empty.1 ⟨v0, hv0⟩)
      · rw [Finset.sum_eq_card_nsmul (fun u hu => hc u hu v0 hv0),
          Finset.sum_eq_card_nsmul (fun v hv => (hc u0 hu0 v hv).symm.trans (hc u0 hu0 v0 hv0)), hcard]
  linarith

open Polynomial in
open QAlgorithms.Papers.Independent.Information100.P53 in
lemma g53h_spec_charpoly {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (s : SpectralData A) :
    A.charpoly = ∏ j, (X - C ((s.value j : ℝ) : ℂ)) := by
  let U : Matrix (Fin q) (Fin q) ℂ := Matrix.of fun i j => s.basis j i
  have hA : A = U * Matrix.diagonal (fun j => ((s.value j : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [s.reconstruct]
    ext i k
    simp [U, Matrix.mul_apply, Matrix.sum_apply, QAlgorithms.pureDensity, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl; intro j _; ring
  have hU : Uᴴ * U = 1 := by
    ext j l
    have := (orthonormal_iff_ite.1 s.basis.orthonormal) j l
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.of_apply, Matrix.one_apply]
    rw [← this]
    simp [dotProduct, mul_comm]
  rw [congrArg Matrix.charpoly hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.charpoly_diagonal]

open Polynomial in
lemma g53h_values_eq {q : ℕ} (v1 v2 : Fin q → ℝ) (h1 : Antitone v1) (h2 : Antitone v2)
    (hc : (∏ j, (X - C ((v1 j : ℝ) : ℂ))) = ∏ j, (X - C ((v2 j : ℝ) : ℂ))) : v1 = v2 := by
  have key : ∀ v : Fin q → ℝ, Antitone v →
      ((∏ j, (X - C ((v j : ℝ) : ℂ))).roots.map RCLike.re).sort (· ≥ ·) = List.ofFn v := by
    intro v hv
    rw [Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp only [Polynomial.roots_X_sub_C]
    have h2 : ((Finset.univ.val.bind fun i : Fin q => ({((v i : ℝ) : ℂ)} : Multiset ℂ)).map RCLike.re)
        = (List.ofFn v : Multiset ℝ) := by
      rw [Multiset.bind_singleton, Multiset.map_map]
      simp [Fin.univ_val_map]
    rw [h2, Multiset.coe_sort, List.mergeSort_of_pairwise]
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hv.sortedGE_ofFn
  have := (key v1 h1).symm.trans (hc ▸ key v2 h2)
  exact List.ofFn_injective this

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.5, §III-D structural simplification under Definition 2: with uniform
prior the top q^n weighted eigenvalues are obtained from M copies of one common
product spectrum. This statement makes no computational runtime claim. -/
theorem solution {n q M : ℕ} (hn : 0 < n) (hq2 : 2 ≤ q)
    (hM : 0 < M) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq : Fintype.card F = q) (rho : F → Matrix (Fin q) (Fin q) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a)) (s : ∀ a, SpectralData (rho a))
    (hsym : IsSymmetric rho) (code : Fin M → Fin n → F)
    (hcode : Function.Injective code) (reference : F)
    (I J : Finset (Fin M × (Fin n → Fin q)))
    (hI : IsTopSelection (q ^ n)
      (productWeight (fun _ => 1 / (M : ℝ)) (fun a => (s a).value) code) I)
    (hJ : IsTopSelection (q ^ n)
      (fun z : Fin M × (Fin n → Fin q) =>
        (1 / (M : ℝ)) * ∏ l, (s reference).value (z.2 l)) J) :
    (∑ z ∈ I, productWeight (fun _ => 1 / (M : ℝ)) (fun a => (s a).value) code z) =
      ∑ z ∈ J, (1 / (M : ℝ)) * ∏ l, (s reference).value (z.2 l) := by
  have hv : ∀ a, (s a).value = (s reference).value := by
    intro a
    obtain ⟨U, hU⟩ := hsym a reference
    have hUU : (U : Matrix (Fin q) (Fin q) ℂ)ᴴ * (U : Matrix (Fin q) (Fin q) ℂ) = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 U.2; rwa [Matrix.star_eq_conjTranspose] at this
    have hc : (rho a).charpoly = (rho reference).charpoly := by
      rw [hU, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    apply g53h_values_eq _ _ (s a).decreasing (s reference).decreasing
    rw [← g53h_spec_charpoly _ (s a), ← g53h_spec_charpoly _ (s reference), hc]
  have hw : productWeight (fun _ => 1 / (M : ℝ)) (fun a => (s a).value) code =
      fun z : Fin M × (Fin n → Fin q) => (1 / (M : ℝ)) * ∏ l, (s reference).value (z.2 l) := by
    funext z; simp only [productWeight, hv]
  rw [hw] at hI ⊢
  exact g53h_top_sum _ _ I J hI hJ



end

