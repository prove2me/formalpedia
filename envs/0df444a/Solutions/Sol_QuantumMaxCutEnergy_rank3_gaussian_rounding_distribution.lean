-- Prove2me | solution 1 for QuantumMaxCutEnergy.rank3_gaussian_rounding_distribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:55:40.909682+00:00
-- url     : https://prove2.me/submissions/b3041d0b-8c59-45e0-a7e5-58d8b4233325

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian
import Theorems.Thm_Grothendieck_matrix_grothendieck_identity
import Theorems.Thm_Grothendieck_ae_mulVecE_ne_zero
import Theorems.Thm_Grothendieck_Er_three_coeff
import Theorems.Thm_Grothendieck_Er_one
import Theorems.Thm_QuantumMaxCutEnergy_rank3_odd_series_ratio_0954

/-!
# The law of the rank-three Gaussian rounding

Briët–de Oliveira Filho–Vallentin's rank-three rounding, in the form the Quantum Max Cut
estimation model uses: for a feasible point `X` of the Max-Cut SDP relaxation, the law `μ` of

  `r i = (G U i) / ‖G U i‖`,  `i : Fin n`,  `G ∈ R^{3×n}` standard Gaussian, `X = U Uᵀ`,

is a probability measure on `(R³)^n` supported on unit vectors whose pair correlations have
mean at most `0.046 + 0.954 * X i j`.

The rank-three identity `E⟪r i, r j⟫ = E_3(X i j)` is the matrix Grothendieck identity
(`Grothendieck.matrix_grothendieck_identity`, Lemma 2.1 of the paper) at rank `3`, and the
scalar inequality `E_3(t) ≤ 0.046 + 0.954 t` is `rank3_odd_series_ratio_0954` applied to the
coefficients `ErCoeff 3` of `E_3`, whose first two values are `8/(3π)` and `4/(15π)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace MatrixOrder

namespace Grothendieck

/-- The coordinate form of the projection to `ℝ^m`. -/
lemma equiv_apply_eq_ofLp {m : Type*} [Fintype m] (x : EuclideanSpace ℝ m) (i : m) :
    (EuclideanSpace.equiv m ℝ) x i = x.ofLp i := by
  rw [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply]

/-- The matrix–vector product in coordinates. -/
lemma mulVecE_eq_coord {r n : ℕ} (Z : Fin r → Fin n → ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    mulVecE r n Z w
      = (EuclideanSpace.equiv (Fin r) ℝ).symm (fun b : Fin r => ∑ x : Fin n, Z b x * w.ofLp x) := by
  simp only [mulVecE]
  have h : (Matrix.of Z).mulVec ((EuclideanSpace.equiv (Fin n) ℝ) w)
      = fun b : Fin r => ∑ x : Fin n, Z b x * w.ofLp x := by
    funext b
    rw [Matrix.mulVec_apply_eq_sum]
    simp [Matrix.of_apply, equiv_apply_eq_ofLp]
  rw [h]

/-- `‖y‖⁻¹ • y` has norm one for `y ≠ 0`. -/
lemma norm_normalize_eq_one {r : ℕ} {y : EuclideanSpace ℝ (Fin r)} (hy : y ≠ 0) :
    ‖normalize r y‖ = 1 := by
  have h : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [normalize, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]

/-- The normalisation map `y ↦ ‖y‖⁻¹ • y` is measurable. -/
lemma measurable_normalize (r : ℕ) : Measurable (normalize r) := by
  unfold normalize
  measurability

end Grothendieck

theorem solution (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) :
    ∃ μ : MeasureTheory.Measure (Fin n → Fin 3 → ℝ),
      MeasureTheory.IsProbabilityMeasure μ ∧
        (∀ᵐ r ∂μ, ∀ i : Fin n, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
          ∀ i j : Fin n,
            ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ ≤ 0.046 + 0.954 * X i j := by
  classical
  -- the coefficients of `E_3` and the scalar certificate
  obtain ⟨hcoef_nonneg, hcoef_summ, hcoef0, hcoef1⟩ := Grothendieck.Er_three_coeff
  have hunit : (∑' k : ℕ, Grothendieck.ErCoeff 3 k) = 1 := by
    have h := Grothendieck.Er_one 3 (by norm_num)
    simpa [Grothendieck.Er, one_pow] using h
  -- a Gram factor of the correlation matrix `X`
  obtain ⟨B, hBB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  have hgram : ∀ i j : Fin n, X i j = ∑ a : Fin n, B a i * B a j := by
    intro i j
    have h1 : X i j = (star B * B) i j := by rw [hBB]
    rw [h1, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : (star B) i a = B a i := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      simp
    rw [h2]
  -- the Bloch vectors
  set u : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (fun a => B a i) with hu
  have hu_coe : ∀ (i a : Fin n), u i a = B a i := fun i a => rfl
  have hinner : ∀ i j : Fin n, inner ℝ (u i) (u j) = X i j := by
    intro i j
    rw [hgram i j, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    exact Finset.sum_congr rfl fun a _ => by rw [hu_coe i a, hu_coe j a]; ring
  have hunorm : ∀ i : Fin n, ‖u i‖ = 1 := by
    intro i
    have hsq : ‖u i‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have hsum : (∑ a : Fin n, (u i a) ^ 2) = X i i := by
        rw [hgram i i]
        exact Finset.sum_congr rfl fun a _ => by rw [hu_coe i a, sq]
      rw [hsum, hdiag i]
    nlinarith [norm_nonneg (u i)]
  have hune : ∀ i : Fin n, u i ≠ 0 := by
    intro i h
    have h1 := hunorm i
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  -- the rounding map and its law
  set φ : (Fin 3 → Fin n → ℝ) → (Fin n → Fin 3 → ℝ) :=
    fun Z i a => (Grothendieck.normalize 3 (Grothendieck.mulVecE 3 n Z (u i))).ofLp a with hφ
  have hφ_meas : Measurable φ := by
    have hfun : φ = fun (Z : Fin 3 → Fin n → ℝ) (i : Fin n) (a : Fin 3) =>
        (Grothendieck.normalize 3 ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          (fun b : Fin 3 => ∑ x : Fin n, Z b x * (u i).ofLp x))).ofLp a := by
      funext Z i a
      simp only [hφ, Grothendieck.mulVecE_eq_coord]
    rw [hfun]
    measurability
  haveI hprob : IsProbabilityMeasure (Grothendieck.gaussianMatrix 3 n) := by
    show IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
      Measure.pi fun _ : Fin n => gaussianReal (0 : ℝ) 1)
    infer_instance
  refine ⟨Measure.map φ (Grothendieck.gaussianMatrix 3 n),
    Measure.isProbabilityMeasure_map hφ_meas.aemeasurable, ?_, ?_⟩
  · -- the law is supported on unit vectors
    rw [MeasureTheory.ae_map_iff hφ_meas.aemeasurable (by measurability)]
    have hne : ∀ᵐ Z ∂(Grothendieck.gaussianMatrix 3 n), ∀ i : Fin n,
        Grothendieck.mulVecE 3 n Z (u i) ≠ 0 := by
      rw [Filter.eventually_all]
      exact fun i => Grothendieck.ae_mulVecE_ne_zero (r := 3) (n := n) (by norm_num) (hune i)
    filter_upwards [hne] with Z hZ i
    have hx : Grothendieck.mulVecE 3 n Z (u i) ≠ 0 := hZ i
    have hnorm1 : ‖Grothendieck.normalize 3 (Grothendieck.mulVecE 3 n Z (u i))‖ = 1 :=
      Grothendieck.norm_normalize_eq_one hx
    have hsq : (∑ a : Fin 3, (φ Z i a) ^ 2) = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hnorm1]
      norm_num
    exact hsq
  · -- the pair correlations
    intro i j
    have hcont : Continuous fun r : Fin n → Fin 3 → ℝ => ∑ a : Fin 3, r i a * r j a := by
      fun_prop
    have hint : ∫ r, (∑ a : Fin 3, r i a * r j a)
          ∂(Measure.map φ (Grothendieck.gaussianMatrix 3 n))
        = ∫ Z, (∑ a : Fin 3, φ Z i a * φ Z j a) ∂(Grothendieck.gaussianMatrix 3 n) :=
      integral_map hφ_meas.aemeasurable hcont.aestronglyMeasurable
    have hGE : (∫ Z, (∑ a : Fin 3, φ Z i a * φ Z j a) ∂(Grothendieck.gaussianMatrix 3 n))
        = Grothendieck.grothendieckExpectation 3 n (u i) (u j) := by
      rw [show Grothendieck.grothendieckExpectation 3 n (u i) (u j)
          = ∫ Z, inner ℝ (Grothendieck.normalize 3 (Grothendieck.mulVecE 3 n Z (u i)))
              (Grothendieck.normalize 3 (Grothendieck.mulVecE 3 n Z (u j)))
              ∂(Grothendieck.gaussianMatrix 3 n) from rfl]
      refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
      exact Finset.sum_congr rfl fun a _ => by simp only [hφ]; ring
    rw [hint, hGE,
      Grothendieck.matrix_grothendieck_identity 3 n (by norm_num) (u i) (u j)
        (hunorm i) (hunorm j), hinner i j]
    -- the scalar certificate `E_3(t) ≤ 0.046 + 0.954 t` on `[-1,1]`
    have habs : |X i j| ≤ 1 := by
      rw [← hinner i j]
      have h := norm_inner_le_norm (𝕜 := ℝ) (u i) (u j)
      rw [hunorm i, hunorm j, mul_one] at h
      simpa using h
    rcases eq_or_lt_of_le (abs_le.mp habs).2 with h1 | h1
    · rw [h1, Grothendieck.Er_one 3 (by norm_num)]
      norm_num
    · have htlow : -1 ≤ X i j := (abs_le.mp habs).1
      have hser := QuantumMaxCutEnergy.rank3_odd_series_ratio_0954
        (fun k : ℕ => Grothendieck.ErCoeff 3 k) hcoef_nonneg hcoef_summ hunit
        (by rw [hcoef0]) (by rw [hcoef1]) (X i j) htlow h1
      have hden : (0 : ℝ) < 1 - X i j := by linarith
      have hkey : 0.954 * (1 - X i j) ≤ 1 - Grothendieck.Er 3 (X i j) := by
        have h := (le_div_iff₀ hden).mp hser
        rw [show Grothendieck.Er 3 (X i j)
            = ∑' k : ℕ, Grothendieck.ErCoeff 3 k * (X i j) ^ (2 * k + 1) from rfl]
        exact h
      linarith
