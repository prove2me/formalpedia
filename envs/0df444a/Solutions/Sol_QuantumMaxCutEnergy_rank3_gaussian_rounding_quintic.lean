-- Prove2me | solution 1 for QuantumMaxCutEnergy.rank3_gaussian_rounding_quintic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:33:01.573496+00:00
-- url     : https://prove2.me/submissions/d939e967-658c-4810-8f34-6788a5502b71

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian
import Theorems.Thm_Grothendieck_matrix_grothendieck_identity
import Theorems.Thm_Grothendieck_ae_mulVecE_ne_zero
import Theorems.Thm_Grothendieck_Er_three_coeff
import Theorems.Thm_Grothendieck_Er_one

open scoped BigOperators

namespace RoundQuintic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Real RealInnerProductSpace MatrixOrder

/-- The coordinate form of the projection to `ℝ^m`. -/
lemma equiv_apply_eq_ofLp {m : Type*} [Fintype m] (x : EuclideanSpace ℝ m) (i : m) :
    (EuclideanSpace.equiv m ℝ) x i = x.ofLp i := by
  rw [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply]

/-- The matrix–vector product in coordinates. -/
lemma mulVecE_eq_coord {r n : ℕ} (Z : Fin r → Fin n → ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    Grothendieck.mulVecE r n Z w
      = (EuclideanSpace.equiv (Fin r) ℝ).symm (fun b : Fin r => ∑ x : Fin n, Z b x * w.ofLp x) := by
  simp only [Grothendieck.mulVecE]
  have h : (Matrix.of Z).mulVec ((EuclideanSpace.equiv (Fin n) ℝ) w)
      = fun b : Fin r => ∑ x : Fin n, Z b x * w.ofLp x := by
    funext b
    rw [Matrix.mulVec_apply_eq_sum]
    simp [Matrix.of_apply, equiv_apply_eq_ofLp]
  rw [h]

/-- `‖y‖⁻¹ • y` has norm one for `y ≠ 0`. -/
lemma norm_normalize_eq_one {r : ℕ} {y : EuclideanSpace ℝ (Fin r)} (hy : y ≠ 0) :
    ‖Grothendieck.normalize r y‖ = 1 := by
  have h : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [Grothendieck.normalize, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]

/-- The normalisation map `y ↦ ‖y‖⁻¹ • y` is measurable. -/
lemma measurable_normalize (r : ℕ) : Measurable (Grothendieck.normalize r) := by
  unfold Grothendieck.normalize
  measurability

/-- The scalar bound: `E_3(t) ≤ t` for `t > 0`, and `E_3(t)` is at most its cubic Taylor
polynomial (with rounded-down coefficients) for `t ≤ 0`. -/
lemma Er3_le_phi (t : ℝ) (hlo : -1 ≤ t) (hhi : t ≤ 1) :
    Grothendieck.Er 3 t ≤ if t ≤ 0 then 0.84882 * t + 0.084882 * t ^ 3 + 0.027283 * t ^ 5 else t := by
  obtain ⟨hnn, hsumm, h0, h1⟩ := Grothendieck.Er_three_coeff
  have hunit : (∑' k : ℕ, Grothendieck.ErCoeff 3 k) = 1 := by
    have h := Grothendieck.Er_one 3 (by norm_num)
    simpa [Grothendieck.Er, one_pow] using h
  split_ifs with ht
  · -- `t ≤ 0`
    have hs0 : 0 ≤ -t := by linarith
    have hs1 : -t ≤ 1 := by linarith
    have hterm : ∀ k : ℕ, 0 ≤ Grothendieck.ErCoeff 3 k * (-t) ^ (2 * k + 1) :=
      fun k => mul_nonneg (hnn k) (pow_nonneg hs0 _)
    have hsummS : Summable (fun k : ℕ => Grothendieck.ErCoeff 3 k * (-t) ^ (2 * k + 1)) := by
      refine Summable.of_nonneg_of_le hterm (fun k => ?_) hsumm
      calc Grothendieck.ErCoeff 3 k * (-t) ^ (2 * k + 1)
          ≤ Grothendieck.ErCoeff 3 k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hs0 hs1) (hnn k)
        _ = Grothendieck.ErCoeff 3 k := mul_one _
    have hEr : Grothendieck.Er 3 t
        = -∑' k : ℕ, Grothendieck.ErCoeff 3 k * (-t) ^ (2 * k + 1) := by
      rw [Grothendieck.Er, ← tsum_neg]
      refine tsum_congr fun k => ?_
      rw [Odd.neg_pow ⟨k, rfl⟩]
      ring
    have hpart := hsummS.sum_le_tsum (Finset.range 3) (fun k _ => hterm k)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hpart
    have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
    have hpipos : 0 < Real.pi := Real.pi_pos
    have hc0 : (0.84882 : ℝ) ≤ Grothendieck.ErCoeff 3 0 := by
      rw [h0, le_div_iff₀ (by positivity)]
      nlinarith
    have hc1 : (0.084882 : ℝ) ≤ Grothendieck.ErCoeff 3 1 := by
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith
    have hCr : Grothendieck.Cr 3 = 8 / (3 * Real.pi) := by
      rw [← h0]
      simp [Grothendieck.ErCoeff, Grothendieck.risingFact]
    have h2 : Grothendieck.ErCoeff 3 2 = 8 / (3 * Real.pi) * (9 / 280) := by
      rw [← hCr]
      simp only [Grothendieck.ErCoeff, Grothendieck.risingFact, Finset.prod_range_succ,
        Finset.prod_range_zero, Nat.factorial]
      norm_num
      ring
    have hc2 : (0.027283 : ℝ) ≤ Grothendieck.ErCoeff 3 2 := by
      rw [h2, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hs3 : 0 ≤ (-t) ^ 3 := pow_nonneg hs0 3
    have hs5 : 0 ≤ (-t) ^ 5 := pow_nonneg hs0 5
    have e2 : (0.027283 : ℝ) * (-t) ^ 5 ≤ Grothendieck.ErCoeff 3 2 * (-t) ^ 5 :=
      mul_le_mul_of_nonneg_right hc2 hs5
    have e0 : (0.84882 : ℝ) * (-t) ≤ Grothendieck.ErCoeff 3 0 * (-t) :=
      mul_le_mul_of_nonneg_right hc0 hs0
    have e1 : (0.084882 : ℝ) * (-t) ^ 3 ≤ Grothendieck.ErCoeff 3 1 * (-t) ^ 3 :=
      mul_le_mul_of_nonneg_right hc1 hs3
    have hpart' : Grothendieck.ErCoeff 3 0 * (-t) + Grothendieck.ErCoeff 3 1 * (-t) ^ 3
        + Grothendieck.ErCoeff 3 2 * (-t) ^ 5
        ≤ ∑' k : ℕ, Grothendieck.ErCoeff 3 k * (-t) ^ (2 * k + 1) := by
      simpa using hpart
    have hcube : (-t) ^ 3 = -(t ^ 3) := by ring
    rw [hEr]
    have hfive : (-t) ^ 5 = -(t ^ 5) := by ring
    rw [hcube] at e1 hpart'
    rw [hfive] at e2 hpart'
    linarith
  · -- `0 < t`
    have ht0 : 0 ≤ t := by linarith
    have hterm : ∀ k : ℕ, Grothendieck.ErCoeff 3 k * t ^ (2 * k + 1)
        ≤ Grothendieck.ErCoeff 3 k * t := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ (hnn k)
      rw [pow_succ]
      calc t ^ (2 * k) * t ≤ 1 * t :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ ht0 hhi) ht0
        _ = t := one_mul _
    have hsummT : Summable (fun k : ℕ => Grothendieck.ErCoeff 3 k * t) := hsumm.mul_right t
    have hsummS : Summable (fun k : ℕ => Grothendieck.ErCoeff 3 k * t ^ (2 * k + 1)) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (hnn k) (pow_nonneg ht0 _)) hterm hsummT
    have hle := hsummS.tsum_le_tsum hterm hsummT
    rw [tsum_mul_right, hunit, one_mul] at hle
    exact hle

/-- The law of the rank-three Gaussian rounding, with the cubic pair-mean bound. -/
lemma rounding_distribution (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) :
    ∃ μ : MeasureTheory.Measure (Fin n → Fin 3 → ℝ),
      MeasureTheory.IsProbabilityMeasure μ ∧
        (∀ᵐ r ∂μ, ∀ i : Fin n, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
          ∀ i j : Fin n,
            ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ ≤
              (if X i j ≤ 0 then 0.84882 * X i j + 0.084882 * (X i j) ^ 3 +
                0.027283 * (X i j) ^ 5 else X i j) := by
  classical
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
      simp only [hφ, mulVecE_eq_coord]
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
      norm_normalize_eq_one hx
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
    have habs : |X i j| ≤ 1 := by
      rw [← hinner i j]
      have h := norm_inner_le_norm (𝕜 := ℝ) (u i) (u j)
      rw [hunorm i, hunorm j, mul_one] at h
      simpa using h
    exact Er3_le_phi (X i j) (abs_le.mp habs).1 (abs_le.mp habs).2

variable {n : ℕ}

/-- Correlation of two Bloch vectors. -/
def pairCorr (r : Fin n → Fin 3 → ℝ) (i j : Fin n) : ℝ :=
  ∑ a : Fin 3, r i a * r j a

lemma continuous_pairCorr (i j : Fin n) :
    Continuous fun r : Fin n → Fin 3 → ℝ => pairCorr r i j := by
  have hi : Continuous fun r : Fin n → Fin 3 → ℝ => r i := continuous_apply i
  have hj : Continuous fun r : Fin n → Fin 3 → ℝ => r j := continuous_apply j
  refine continuous_finsetSum _ fun a _ => ?_
  exact ((continuous_apply a).comp hi).mul ((continuous_apply a).comp hj)

lemma abs_pairCorr_le_one (r : Fin n → Fin 3 → ℝ)
    (hr : ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) (i j : Fin n) : |pairCorr r i j| ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun a => r i a) (fun a => r j a)
  simp only [hr i, hr j, mul_one] at h
  have h2 : (pairCorr r i j) ^ 2 ≤ 1 := by simpa [pairCorr] using h
  rw [abs_le]
  constructor <;> nlinarith [h2, sq_nonneg (pairCorr r i j - 1), sq_nonneg (pairCorr r i j + 1)]

lemma integrable_pairCorr (μ : Measure (Fin n → Fin 3 → ℝ)) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ r ∂μ, ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) (i j : Fin n) :
    Integrable (fun r => pairCorr r i j) μ := by
  refine Integrable.of_bound (continuous_pairCorr i j).aestronglyMeasurable 1 ?_
  filter_upwards [hunit] with r hr
  simpa [Real.norm_eq_abs] using abs_pairCorr_le_one r hr i j

/-- **The probabilistic method step.**  If a probability distribution on Bloch assignments
has pair correlations bounded by `b i j` in mean, then some single assignment satisfies the
weighted inequality for every nonnegative weighting `w`. -/
lemma rounding_of_expectation_bound (w : QuantumMaxCutEnergy.Edge n → ℝ) (hw0 : ∀ e, 0 ≤ w e)
    (b : Fin n → Fin n → ℝ)
    (μ : Measure (Fin n → Fin 3 → ℝ)) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ r ∂μ, ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1)
    (hbound : ∀ i j : Fin n, ∫ r, pairCorr r i j ∂μ ≤ b i j) :
    ∃ r : Fin n → Fin 3 → ℝ, (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
      ∑ e : QuantumMaxCutEnergy.Edge n, w e * pairCorr r e.val.1 e.val.2 ≤
        ∑ e : QuantumMaxCutEnergy.Edge n, w e * b e.val.1 e.val.2 := by
  classical
  set F : (Fin n → Fin 3 → ℝ) → ℝ :=
    fun r => ∑ e : QuantumMaxCutEnergy.Edge n, w e * pairCorr r e.val.1 e.val.2 with hF
  set B : ℝ := ∑ e : QuantumMaxCutEnergy.Edge n, w e * b e.val.1 e.val.2 with hB
  have hFcont : Continuous F := by
    rw [hF]
    exact continuous_finsetSum _ fun e _ => (continuous_pairCorr _ _).const_mul _
  have hFint : Integrable F μ := by
    refine Integrable.of_bound hFcont.aestronglyMeasurable
      (∑ e : QuantumMaxCutEnergy.Edge n, w e) ?_
    filter_upwards [hunit] with r hr
    rw [Real.norm_eq_abs, hF]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun e _ => ?_
    have hw : (0:ℝ) ≤ w e := hw0 e
    rw [abs_mul, abs_of_nonneg hw]
    calc w e * |pairCorr r e.val.1 e.val.2| ≤ w e * 1 :=
          mul_le_mul_of_nonneg_left (abs_pairCorr_le_one r hr _ _) hw
      _ = w e := mul_one _
  have hIntF : ∫ r, F r ∂μ =
      ∑ e : QuantumMaxCutEnergy.Edge n, w e * ∫ r, pairCorr r e.val.1 e.val.2 ∂μ := by
    rw [hF, integral_finsetSum Finset.univ
      (fun e _ => (integrable_pairCorr μ hunit _ _).const_mul _)]
    exact Finset.sum_congr rfl fun e _ => integral_const_mul _ _
  have hle : ∫ r, F r ∂μ ≤ B := by
    rw [hIntF, hB]
    refine Finset.sum_le_sum fun e _ => ?_
    exact mul_le_mul_of_nonneg_left (hbound _ _) (hw0 e)
  by_contra hcon
  have hpoint : ∀ r, (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) → B < F r := by
    intro r hr
    by_contra hle'
    exact hcon ⟨r, hr, not_lt.mp hle'⟩
  have hnull : μ {r : Fin n → Fin 3 → ℝ | ¬ (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1)} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact hunit
  have hGmeas : Measurable fun r : Fin n → Fin 3 → ℝ => F r - B :=
    hFcont.measurable.sub measurable_const
  have hSmeas : MeasurableSet {r : Fin n → Fin 3 → ℝ | 0 < F r - B} :=
    measurableSet_lt measurable_const hGmeas
  have hScompl : μ {r : Fin n → Fin 3 → ℝ | 0 < F r - B}ᶜ = 0 := by
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro r hr
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hr
    simp only [Set.mem_ofPred_eq]
    intro hu
    have := hpoint r hu
    linarith
  have hSprob : μ {r : Fin n → Fin 3 → ℝ | 0 < F r - B} = 1 := by
    have h := MeasureTheory.measure_add_measure_compl (μ := μ) hSmeas
    rw [hScompl, add_zero, MeasureTheory.measure_univ] at h
    exact h
  have hsupp : 0 < μ (Function.support fun r : Fin n → Fin 3 → ℝ => F r - B) := by
    have h₁ : μ {r : Fin n → Fin 3 → ℝ | 0 < F r - B} ≤
        μ (Function.support fun r : Fin n → Fin 3 → ℝ => F r - B) := by
      refine MeasureTheory.measure_mono ?_
      intro r hr
      simp only [Set.mem_ofPred_eq] at hr
      simp only [Function.mem_support, ne_eq]
      linarith
    rw [hSprob] at h₁
    exact lt_of_lt_of_le one_pos h₁
  have hGnonneg : 0 ≤ᵐ[μ] fun r : Fin n → Fin 3 → ℝ => F r - B := by
    filter_upwards [hunit] with r hr
    have h2 := hpoint r hr
    show (0:ℝ) ≤ F r - B
    linarith
  have hGint : Integrable (fun r : Fin n → Fin 3 → ℝ => F r - B) μ :=
    hFint.sub (integrable_const B)
  have hpos : 0 < ∫ r, (F r - B) ∂μ := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hGnonneg hGint]
    exact hsupp
  have hBint : ∫ r : Fin n → Fin 3 → ℝ, B ∂μ = B := by
    rw [MeasureTheory.integral_const, MeasureTheory.Measure.real_def, MeasureTheory.measure_univ]
    simp
  rw [MeasureTheory.integral_sub hFint (integrable_const B), hBint] at hpos
  linarith

end

end RoundQuintic

theorem solution (n : ℕ)
    (a : QuantumMaxCutEnergy.Edge n → ℝ) (ha : ∀ e, 0 ≤ a e)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    ∃ r : Fin n → Fin 3 → ℝ,
      (∀ i, ∑ b : Fin 3, (r i b) ^ 2 = 1) ∧
      (∑ e : QuantumMaxCutEnergy.Edge n, a e *
          (∑ b : Fin 3, r e.val.1 b * r e.val.2 b)) ≤
        ∑ e : QuantumMaxCutEnergy.Edge n, a e *
          (if X e.val.1 e.val.2 ≤ 0 then
            0.84882 * X e.val.1 e.val.2 + 0.084882 * (X e.val.1 e.val.2) ^ 3 +
              0.027283 * (X e.val.1 e.val.2) ^ 5
          else X e.val.1 e.val.2) := by
  obtain ⟨μ, hμ, hunit, hbound⟩ := RoundQuintic.rounding_distribution n X hX hdiag
  exact @RoundQuintic.rounding_of_expectation_bound n a ha
    (fun i j => if X i j ≤ 0 then 0.84882 * X i j + 0.084882 * (X i j) ^ 3 +
      0.027283 * (X i j) ^ 5 else X i j)
    μ hμ hunit hbound
