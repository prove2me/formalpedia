-- Prove2me | solution 1 for SpikedWishart.Separated.theorem_1_1_b
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:30:02.981214+00:00
-- url     : https://prove2.me/submissions/e8b846bd-0ea2-4ea8-bfec-7cb51fb4c4a5

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
import Theorems.Thm_SpikedWishart_Separated_null_wishart_top_eigenvalue_edge_rate
import Theorems.Thm_SpikedWishart_Separated_null_wishart_truncated_resolvent_trace_moments
import Theorems.Thm_SpikedWishart_Separated_null_wishart_resolvent_trace_limit_of_moments
import Theorems.Thm_SpikedWishart_Separated_null_wishart_resolvent_trace_square_limit_of_trace_limit
import Theorems.Thm_SpikedWishart_Separated_gaussian_sesquilinear_form_clt
import Theorems.Thm_SpikedWishart_Separated_spiked_block_psd_limit_of_sesquilinear_clt
import Theorems.Thm_SpikedWishart_Separated_gue_top_eigenvalue_cdf

set_option autoImplicit false
set_option linter.all false

open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder
open Filter Topology MeasureTheory
open Matrix
open scoped ComplexOrder Pointwise
open Filter Topology MeasureTheory Set

namespace SpikedWishart.Separated.Lib

-- ===== from ChildStatements.lean =====
section

/-- P2 (sharp edge of the null complex Wishart matrix; Geman 1980, Bai-Silverstein-Yin 1988, for Gaussian
entries also Davidson-Szarek 2001 Thm II.13): with `N n ≤ M n` and `N n → ∞`, the largest eigenvalue of
`(1/M) G Gᴴ` exceeds `(1 + √(N/M))² + ε` with probability tending to `0`. -/
def P2_nullEdge : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (M N : ℕ → ℕ), Tendsto N atTop atTop → (∀ n, N n ≤ M n) →
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X})
      atTop (𝓝 0)

/-- Q2 (resolvent statistics of the null Wishart outside the bulk; Bai-Silverstein 2004 / Bai-Yao
2008 Lemma 6.1): `Y` the `p × M` Gaussian matrix, `W = (1/M) Y Yᴴ`, `x = 1/ψ + y/(1-ψ)` with
`ψ` strictly inside `(0, 1/(1+√y))` (so `x` is right of the edge `(1+√y)²`), `y = p/M + O(1/M)`,
`A = 1 + (1/M) Yᴴ (x - W)⁻¹ Y` (`= x (x - YᴴY/M)⁻¹`). Then
`√M ((1/M) tr A - x ψ) → 0` and `(1/M) tr A² - x²/(ψ⁻² - y(1-ψ)⁻²) → 0` in probability. -/
def Q2_resolvent : Prop :=
  ∀ (C₀ ψ₀ δ : ℝ), 0 < ψ₀ → 0 < δ → ∀ (M p : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, p n ≤ M n) →
    ∀ (y ψ : ℕ → ℝ), (∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n) →
    (∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) →
    ∀ ε : ℝ, 0 < ε →
    let x : ℕ → ℝ := fun n => 1 / ψ n + y n / (1 - ψ n)
    let A : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n X =>
      1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x n : ℂ) • 1 - (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |Real.sqrt (M n) * ((((A n X).trace).re / M n) - x n * ψ n)|}) atTop (𝓝 0) ∧
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |((A n X * A n X).trace).re / M n -
          x n ^ 2 / ((ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2)|}) atTop (𝓝 0)

/-- E (edge bound with polynomial rate; Bai-Silverstein 2004 (1.9a), for Gaussian entries also
Davidson-Szarek 2001 Thm II.13): for `N n ≤ M n`, `M n → ∞` and every power `l`,
`M^l · P(λmax((1/M) G Gᴴ) > (1 + √(N/M))² + ε) → 0`. -/
def P2_edgeRate : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (l : ℕ) (M N : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, N n ≤ M n) →
    Tendsto (fun n => (M n : ℝ) ^ l * (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X})
      atTop (𝓝 0)

/-- Q2.M (variance and self-consistent equation for the truncated resolvent trace; Efron-Stein and the
Marchenko-Pastur equation, Bai-Silverstein 2010 Ch. 3): `F = 1_{W ⪯ e1} Re tr (x - W)⁻¹`, `c = E F / M`. -/
def Q2_moments : Prop :=
  ∀ (M p : ℕ), 0 < M → ∀ (x e1 : ℝ), 0 ≤ e1 → e1 < x →
    let μ := SpikedWishart.SoftEdge.sampleLaw M p
    let good : Set (Fin M → Fin p → ℂ) :=
      {X | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ)).PosSemidef}
    let F : (Fin M → Fin p → ℂ) → ℝ := good.indicator (fun X =>
      (trace (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹)).re)
    let Pb : ℝ := μ.real goodᶜ
    let c : ℝ := (∫ X, F X ∂μ) / M
    let κ : ℝ := (x - e1) / (2 * x)
    let a : ℝ := (x - e1)⁻¹
    let K : ℝ := 2 / κ ^ 2 * ((M : ℝ)⁻¹) ^ 2 * (p * a ^ 4) +
      8 * ((M : ℝ)⁻¹ * (p * a ^ 2)) ^ 2 / κ ^ 4 * ((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2)
    let B : ℝ := p * a + 2 * ((M : ℝ)⁻¹ * (p * a ^ 2)) / κ
    (∫ X, (F X - ∫ Y, F Y ∂μ) ^ 2 ∂μ ≤ M * (K + B ^ 2 * Pb)) ∧
    ((((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + Pb) / 2 + (M : ℝ)⁻¹ * (a / κ) ≤ κ / 2 →
      0 ≤ c ∧ c ≤ 1 - κ / 2 ∧
      |x * c - p / M - c / (1 - c)| ≤
        4 / κ ^ 2 * ((((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + Pb) / 2 + Pb + (M : ℝ)⁻¹ * (a / κ)) +
        4 / κ ^ 3 * (4 * (((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + (K + B ^ 2 * Pb) / M + Pb +
          ((M : ℝ)⁻¹ * (a / κ)) ^ 2)) +
        ((p : ℝ) / M + 2 / κ) * Pb)

/-- Q2 part (i): `√M ((1/M) tr A - x ψ) → 0` in probability. -/
def Q2_part1 : Prop :=
  ∀ (C₀ ψ₀ δ : ℝ), 0 < ψ₀ → 0 < δ → ∀ (M p : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, p n ≤ M n) →
    ∀ (y ψ : ℕ → ℝ), (∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n) →
    (∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) →
    ∀ ε : ℝ, 0 < ε →
    let x : ℕ → ℝ := fun n => 1 / ψ n + y n / (1 - ψ n)
    let A : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n X =>
      1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x n : ℂ) • 1 - (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |Real.sqrt (M n) * ((((A n X).trace).re / M n) - x n * ψ n)|}) atTop (𝓝 0)

/-- Q2 part (ii): `(1/M) tr A² - x²/(ψ⁻² - y(1-ψ)⁻²) → 0` in probability. -/
def Q2_part2 : Prop :=
  ∀ (C₀ ψ₀ δ : ℝ), 0 < ψ₀ → 0 < δ → ∀ (M p : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, p n ≤ M n) →
    ∀ (y ψ : ℕ → ℝ), (∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n) →
    (∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) →
    ∀ ε : ℝ, 0 < ε →
    let x : ℕ → ℝ := fun n => 1 / ψ n + y n / (1 - ψ n)
    let A : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n X =>
      1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x n : ℂ) • 1 - (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |((A n X * A n X).trace).re / M n -
          x n ^ 2 / ((ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2)|}) atTop (𝓝 0)

/-- Child: part (i) from the moment bounds and the edge rate (Chebyshev + root selection). -/
def Q2_part1_of : Prop := Q2_moments → P2_edgeRate → Q2_part1

/-- Child: part (ii) from part (i) and the edge rate (convexity of `z ↦ tr A(z)/M`). -/
def Q2_part2_of : Prop := Q2_part1 → P2_edgeRate → Q2_part2

/-- DL (conditional limit of the spiked block; Baik-Ben Arous-Peche 2005, proof of Thm 1.1(b), Section 3,
the step after conditioning on the null block): for deterministic Hermitian `A_n` with `-C ≤ A_n ≤ C`,
`s₀ ≤ (1/M) tr A_n² ≤ S₁`, spike block `D_n = diag(L_n,…,L_n, d)` and shifts `x_n` with
`√M (x_n - L_n (1/M) tr A_n) / (L_n √((1/M) tr A_n²)) → t`, the probability that
`x_n - (1/M) D^{1/2} Hᵀ A_n H̄ D^{1/2}` is positive semidefinite (`H` an `M × (k+q)` complex Gaussian array)
tends to `G k t`. -/
def DL_blockLimit : Prop :=
  ∀ (k q : ℕ), 1 ≤ k → ∀ (C s₀ S₁ c x₀ : ℝ), 0 < s₀ → 0 < c → 0 < x₀ →
    ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    (∀ n, ((A n * A n).trace).re / M n ≤ S₁) →
    ∀ (L : ℕ → ℝ), (∀ n, c ≤ L n ∧ L n ≤ C) →
    ∀ (D : ℕ → Fin (k + q) → ℝ), (∀ n i, D n (Fin.castAdd q i) = L n) →
    (∀ n j, c ≤ D n (Fin.natAdd k j) ∧ D n (Fin.natAdd k j) ≤ L n - c) →
    ∀ (x : ℕ → ℝ), (∀ n, x₀ ≤ x n) → ∀ (t : ℝ),
    Tendsto (fun n => Real.sqrt (M n) * (x n - L n * (((A n).trace).re / M n)) /
        (L n * Real.sqrt (((A n * A n).trace).re / M n))) atTop (𝓝 t) →
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
      {X | ((x n : ℂ) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ) -
        (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
          ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ)))).PosSemidef})
      atTop (𝓝 (G k t))

end

-- ===== from Slutsky.lean =====
section

end

-- ===== from LamMax.lean =====
section

variable {k : ℕ}

/-- The quadratic form of a Hermitian matrix is real. -/
theorem im_quad_eq_zero {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) (x : Fin k → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  have h : star (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (A *ᵥ x) := by
    simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : star (A j i) = A i j := by
      have := congrFun (congrFun hA i) j
      simpa [conjTranspose_apply] using this
    rw [hij]; ring
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem psd_iff_re {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ x : Fin k → ℂ, 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x
    exact (Complex.nonneg_iff.mp (h x)).1
  · intro h
    refine ⟨hA, fun x => Complex.nonneg_iff.mpr ⟨h x, (im_quad_eq_zero hA x).symm⟩⟩

/-- The Hermitian part `(H + Hᴴ)/2` of an array. -/
noncomputable def herm (H : Fin k → Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  (1 / 2 : ℂ) • (Matrix.of H + (Matrix.of H)ᴴ)

theorem herm_isHermitian (H : Fin k → Fin k → ℂ) : (herm H).IsHermitian := by
  unfold herm
  ext i j
  simp [conjTranspose_apply] <;> ring

theorem herm_of_isHermitian (H : Fin k → Fin k → ℂ) (hH : (Matrix.of H).IsHermitian) :
    herm H = Matrix.of H := by
  unfold herm
  rw [hH.eq]
  ext i j
  simp [Matrix.smul_apply] <;> ring

/-- The unit sphere `Σ |v_i|² = 1`. -/
def sph (k : ℕ) : Set (Fin k → ℂ) := {v | ∑ i, Complex.normSq (v i) = 1}

theorem isCompact_sph : IsCompact (sph k) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin k → ℂ)) (r := 1)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : Complex.normSq (v i) ≤ 1 := by
      rw [← hv]
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
    rw [Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (v i)]

/-- The quadratic form, as a jointly continuous function. -/
noncomputable def quad (H : Fin k → Fin k → ℂ) (v : Fin k → ℂ) : ℝ := (star v ⬝ᵥ (herm H *ᵥ v)).re

theorem continuous_quad : Continuous ↿(quad (k := k)) := by
  unfold quad herm
  simp only [dotProduct, mulVec, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    conjTranspose_apply, Pi.star_apply]
  fun_prop

/-- `λ_max` of the Hermitian part, as a sup over the unit sphere (continuous). -/
noncomputable def phi (H : Fin k → Fin k → ℂ) : ℝ := sSup (quad H '' sph k)

theorem continuous_phi : Continuous (phi (k := k)) :=
  isCompact_sph.continuous_sSup continuous_quad

theorem re_star_self (x : Fin k → ℂ) : (star x ⬝ᵥ x).re = ∑ i, Complex.normSq (x i) := by
  simp [dotProduct, Complex.normSq_apply, Complex.mul_re]

theorem quad_smul (H : Fin k → Fin k → ℂ) (x : Fin k → ℂ) (a : ℝ) :
    quad H ((a : ℂ) • x) = a ^ 2 * quad H x := by
  unfold quad
  rw [mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im]
  ring

theorem phi_le_iff (hk : 1 ≤ k) (H : Fin k → Fin k → ℂ) (t : ℝ) :
    phi H ≤ t ↔ ((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - herm H).PosSemidef := by
  have hherm : ((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - herm H).IsHermitian := by
    refine IsHermitian.sub ?_ (herm_isHermitian H)
    simp [IsHermitian, conjTranspose_smul]
  have hquad : ∀ x : Fin k → ℂ, (star x ⬝ᵥ (((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - herm H) *ᵥ x)).re
      = t * ∑ i, Complex.normSq (x i) - quad H x := by
    intro x
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, Complex.sub_re,
      ← re_star_self]
    unfold quad
    simp [Complex.mul_re]
  have hne : (sph k).Nonempty := by
    refine ⟨Pi.single ⟨0, hk⟩ 1, ?_⟩
    simp [sph, Pi.single_apply, Finset.sum_ite_eq']
  have hbdd : BddAbove (quad H '' sph k) :=
    (isCompact_sph.image_of_continuousOn
      (continuous_quad.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn).bddAbove
  rw [psd_iff_re hherm, phi, csSup_le_iff hbdd (hne.image _)]
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hquad]
  constructor
  · intro h x
    by_cases hx : ∑ i, Complex.normSq (x i) = 0
    · have hx0 : x = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp hx i
          (Finset.mem_univ i)
        simpa using this
      subst hx0
      simp [quad]
    · have hpos : 0 < ∑ i, Complex.normSq (x i) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (x j)) (Ne.symm hx)
      set s := ∑ i, Complex.normSq (x i)
      set a := 1 / Real.sqrt s
      have ha2 : a ^ 2 = 1 / s := by
        rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
      have hv : ((a : ℂ) • x) ∈ sph k := by
        simp only [sph, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
          Complex.normSq_ofReal, ← Finset.mul_sum]
        rw [← sq, ha2]; field_simp; rfl
      have := h _ hv
      rw [quad_smul, ha2] at this
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos] at this
      linarith
  · intro h v hv
    have := h v
    rw [show ∑ i, Complex.normSq (v i) = 1 from hv] at this
    linarith

end

-- ===== from Perturb.lean =====
section

end

-- ===== from Split.lean =====
section

/-- One row of i.i.d. coordinates splits along `e : ι ≃ α ⊕ β` into two independent rows. -/
theorem row_split_measurePreserving {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (e : ι ≃ α ⊕ β) :
    MeasurePreserving (fun v : ι → ℂ => ((fun a => v (e.symm (Sum.inl a))),
        (fun b => v (e.symm (Sum.inr b)))))
      (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : α => μ).prod (Measure.pi fun _ : β => μ)) := by
  have h1 := measurePreserving_piCongrLeft (α := fun _ : α ⊕ β => ℂ) (fun _ => μ) e
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : α ⊕ β => ℂ) (fun _ => μ)
  have h := h2.comp h1
  convert h using 1
  funext v
  simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft]
  ext a
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]

/-- The `M`-sample Gaussian array splits along `e : ι ≃ α ⊕ β` (coordinates) into two independent
arrays. -/
theorem array_split_measurePreserving {M : ℕ} {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (e : ι ≃ α ⊕ β) :
    MeasurePreserving (fun X : Fin M → ι → ℂ => ((fun k a => X k (e.symm (Sum.inl a))),
        (fun k b => X k (e.symm (Sum.inr b)))))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : α => μ).prod
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : β => μ)) := by
  have h1 := measurePreserving_pi (fun _ : Fin M => Measure.pi fun _ : ι => μ)
    (fun _ : Fin M => (Measure.pi fun _ : α => μ).prod (Measure.pi fun _ : β => μ))
    (fun _ => row_split_measurePreserving μ e)
  have h2 := measurePreserving_arrowProdEquivProdArrow (α → ℂ) (β → ℂ) (Fin M)
    (fun _ => Measure.pi fun _ : α => μ) (fun _ => Measure.pi fun _ : β => μ)
  exact h2.comp h1

/-- The sample law splits: `sampleLaw M N = sampleLaw M r ⊗ sampleLaw M p` along `e`. -/
theorem sampleLaw_split {M N r p : ℕ} (e : Fin N ≃ Fin r ⊕ Fin p) :
    MeasurePreserving (fun X : Fin M → Fin N → ℂ => ((fun k a => X k (e.symm (Sum.inl a))),
        (fun k b => X k (e.symm (Sum.inr b)))))
      (SpikedWishart.SoftEdge.sampleLaw M N)
      ((SpikedWishart.SoftEdge.sampleLaw M r).prod (SpikedWishart.SoftEdge.sampleLaw M p)) :=
  array_split_measurePreserving _ e

end

-- ===== from Block.lean =====
section

/-- `2xy ≤ u x² + y²/u`. -/
theorem two_mul_le_amgm (x y u : ℝ) (hu : 0 < u) : 2 * (x * y) ≤ u * x ^ 2 + y ^ 2 / u := by
  have h0 : 0 ≤ (u * x - y) ^ 2 / u := div_nonneg (sq_nonneg _) hu.le
  have e : (u * x - y) ^ 2 / u = u * x ^ 2 + y ^ 2 / u - 2 * (x * y) := by
    field_simp
    ring
  linarith

section block

variable {k q : ℕ}

end block

end

-- ===== from DetLimit.lean =====
section

end

-- ===== from Misc.lean =====
section

/-- Diagonal extraction: convergence in probability for every fixed `ε` gives one sequence
`ε_n → 0` with `P_n(ε_n) → 0`. -/
theorem diag_seq (P : ℕ → ℝ → ℝ) (hP : ∀ ε, 0 < ε → Tendsto (fun n => P n ε) atTop (𝓝 0)) :
    ∃ e : ℕ → ℝ, (∀ n, 0 < e n) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ δ, 0 < δ → ∀ᶠ n in atTop, P n (e n) < δ := by
  classical
  have hN : ∀ j : ℕ, ∃ N, ∀ n ≥ N, P n (1 / ((j : ℝ) + 1)) < 1 / ((j : ℝ) + 1) := fun j => by
    have h := (tendsto_order.1 (hP (1 / ((j : ℝ) + 1)) (by positivity))).2 _
      (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))
    exact eventually_atTop.mp h
  choose N hNspec using hN
  let J : ℕ → ℕ := fun n => Nat.findGreatest (fun j => ∀ i ≤ j, N i ≤ n) n
  have hJgood : ∀ n, N 0 ≤ n → N (J n) ≤ n := fun n hn =>
    (Nat.findGreatest_spec (P := fun j => ∀ i ≤ j, N i ≤ n) (Nat.zero_le n) (fun i hi => by
      rw [Nat.le_zero.mp hi]; exact hn)) (J n) le_rfl
  have hJlarge : ∀ j, ∀ᶠ n in atTop, j ≤ J n := fun j => by
    refine eventually_atTop.2 ⟨j + ∑ i ∈ Finset.range (j + 1), N i, fun n hn => ?_⟩
    refine Nat.le_findGreatest (by omega) fun i hi => ?_
    have : N i ≤ ∑ i ∈ Finset.range (j + 1), N i :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    omega
  have hmono : ∀ j n, j ≤ J n → 1 / ((J n : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := fun j n h => by
    have : (j : ℝ) + 1 ≤ (J n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right h 1
    exact one_div_le_one_div_of_le (by positivity) this
  refine ⟨fun n => 1 / ((J n : ℝ) + 1), fun n => by positivity, ?_, ?_⟩
  · rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (by positivity),
      fun a ha => ?_⟩
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt ha
    filter_upwards [hJlarge j] with n hn
    exact lt_of_le_of_lt (hmono j n hn) hj
  · intro δ hδ
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    filter_upwards [hJlarge j, eventually_ge_atTop (N 0)] with n hn hn0
    have h1 := hNspec (J n) n (hJgood n hn0)
    have h2 := hmono j n hn
    linarith

/-- `re ⟨v, (a - Yᴴ Y) v⟩ = a |v|² - |Y v|²`. -/
theorem re_quad_sub_gram {p M : ℕ} (Y : Matrix (Fin p) (Fin M) ℂ) (a : ℝ) (v : Fin M → ℂ) :
    (star v ⬝ᵥ (((a : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) - Yᴴ * Y) *ᵥ v)).re =
      a * ∑ i, Complex.normSq (v i) - ∑ i, Complex.normSq ((Y *ᵥ v) i) := by
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, smul_mulVec, one_mulVec, dotProduct_smul,
    ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, smul_eq_mul, Complex.re_ofReal_mul,
    re_star_self, re_star_self]

theorem isHermitian_smul_one_sub_gram {p M : ℕ} (Y : Matrix (Fin p) (Fin M) ℂ) (a : ℝ) :
    ((a : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) - Yᴴ * Y).IsHermitian := by
  refine IsHermitian.sub (isHermitian_one.smul ?_) (isHermitian_conjTranspose_mul_self Y)
  show star (a : ℂ) = a
  simp

/-- `‖Y‖² ≤ a` transfers between `Y Yᴴ` and `Yᴴ Y`. -/
theorem psd_swap {p M : ℕ} (Y : Matrix (Fin p) (Fin M) ℂ) (a : ℝ) (ha : 0 ≤ a)
    (h : ((a : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Y * Yᴴ).PosSemidef) :
    ((a : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) - Yᴴ * Y).PosSemidef := by
  have h' : ∀ u : Fin p → ℂ, ∑ i, Complex.normSq ((Yᴴ *ᵥ u) i) ≤ a * ∑ i, Complex.normSq (u i) := by
    intro u
    have h2 : ((a : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Yᴴᴴ * Yᴴ).PosSemidef := by
      rwa [conjTranspose_conjTranspose]
    have := ((psd_iff_re (isHermitian_smul_one_sub_gram Yᴴ a)).mp h2) u
    rw [re_quad_sub_gram] at this
    linarith
  rw [psd_iff_re (isHermitian_smul_one_sub_gram Y a)]
  intro v
  rw [re_quad_sub_gram]
  have hW : ∑ i, Complex.normSq ((Y *ᵥ v) i) = (star (Yᴴ *ᵥ (Y *ᵥ v)) ⬝ᵥ v).re := by
    rw [star_mulVec Yᴴ (Y *ᵥ v), conjTranspose_conjTranspose, ← dotProduct_mulVec, re_star_self]
  have hre : (star (Yᴴ *ᵥ (Y *ᵥ v)) ⬝ᵥ v).re ≤
      ∑ i, ‖(Yᴴ *ᵥ (Y *ᵥ v)) i‖ * ‖v i‖ := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖(Yᴴ *ᵥ (Y *ᵥ v)) i‖)
    (fun i => ‖v i‖)
  simp only [← Complex.normSq_eq_norm_sq] at hcs
  have hZ := h' (Y *ᵥ v)
  have hW0 : 0 ≤ ∑ i, Complex.normSq ((Y *ᵥ v) i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hV0 : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hS0 : 0 ≤ ∑ i, ‖(Yᴴ *ᵥ (Y *ᵥ v)) i‖ * ‖v i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  generalize ∑ i, Complex.normSq ((Y *ᵥ v) i) = W at *
  generalize ∑ i, Complex.normSq (v i) = V at *
  generalize ∑ i, ‖(Yᴴ *ᵥ (Y *ᵥ v)) i‖ * ‖v i‖ = S at *
  generalize ∑ i, Complex.normSq ((Yᴴ *ᵥ (Y *ᵥ v)) i) = Z at *
  have hWS : W ≤ S := hW ▸ hre
  have hW2 : W * W ≤ W * (a * V) := by
    have h1 : W ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hW0 hWS 2
    have h2 : Z * V ≤ a * W * V := mul_le_mul_of_nonneg_right hZ hV0
    nlinarith
  rcases hW0.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith
  · have := le_of_mul_le_mul_left hW2 hpos
    linarith

end

-- ===== from ABounds.lean =====
section

/-- (needs Block.lean `two_mul_le_amgm` and LamMax.lean `re_star_self`) -/
theorem re_dot_le_amgm {n : ℕ} (w u : Fin n → ℂ) (t : ℝ) (ht : 0 < t) :
    (star w ⬝ᵥ u).re ≤ (t * ∑ i, Complex.normSq (u i) + (∑ i, Complex.normSq (w i)) / t) / 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := two_mul_le_amgm ‖u i‖ ‖w i‖ t ht
  have h2 : (star (w i) * u i).re ≤ ‖u i‖ * ‖w i‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_star, mul_comm]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  linarith

theorem re_quad_smul_one {n : ℕ} (C : ℝ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (((C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v)).re = C * ∑ i, Complex.normSq (v i) := by
  rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, re_star_self]

/-- Resolvent bounds: if `lam - S ⪰ 0` with `lam < x`, then for `R = (x - S)⁻¹`,
`0 ≤ ⟨w, R w⟩ ≤ |w|² / (x - lam)`. -/
theorem resolvent_quad_bounds {p : ℕ} (S : Matrix (Fin p) (Fin p) ℂ) (x lam : ℝ) (hx : lam < x)
    (hS : ((lam : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - S).PosSemidef) (w : Fin p → ℂ) :
    0 ≤ (star w ⬝ᵥ (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - S)⁻¹ *ᵥ w)).re ∧
      (star w ⬝ᵥ (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - S)⁻¹ *ᵥ w)).re ≤
        (∑ i, Complex.normSq (w i)) / (x - lam) := by
  set P := (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - S with hP
  have hSH : S.IsHermitian := by
    have h1 := hS.isHermitian
    have h2 : ((lam : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)).IsHermitian :=
      isHermitian_one.smul (show star (lam : ℂ) = lam by simp)
    have := h2.sub h1
    simpa using this
  have hPH : P.IsHermitian := (isHermitian_one.smul (show star (x : ℂ) = x by simp)).sub hSH
  have hPdecomp : P = (((x - lam : ℝ)) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) +
      ((lam : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - S) := by
    rw [hP]; push_cast; rw [sub_smul]; abel
  have hlow : ∀ u : Fin p → ℂ, (x - lam) * ∑ i, Complex.normSq (u i) ≤ (star u ⬝ᵥ (P *ᵥ u)).re := by
    intro u
    have h0 := (psd_iff_re hS.isHermitian).mp hS u
    rw [hPdecomp, add_mulVec, dotProduct_add, Complex.add_re, re_quad_smul_one]
    linarith
  have hxl : 0 < x - lam := by linarith
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := hlow u
    rw [hu, dotProduct_zero, Complex.zero_re] at this
    have hs : ∑ i, Complex.normSq (u i) = 0 := by
      have hnn : 0 ≤ ∑ i, Complex.normSq (u i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
      nlinarith
    apply hu0
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (u i))).mp hs i
      (Finset.mem_univ i)
    simpa using this
  have hinv : P * P⁻¹ = 1 := mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hdet)
  set u := P⁻¹ *ᵥ w with hu
  have hPu : P *ᵥ u = w := by rw [hu, mulVec_mulVec, hinv, one_mulVec]
  have hkey : (star w ⬝ᵥ u).re = (star u ⬝ᵥ (P *ᵥ u)).re := by
    conv_lhs => rw [← hPu]
    rw [star_mulVec, ← dotProduct_mulVec, hPH.eq]
  rw [hkey]
  have h1 := hlow u
  have hu0 : 0 ≤ ∑ i, Complex.normSq (u i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  refine ⟨le_trans (mul_nonneg hxl.le hu0) h1, ?_⟩
  have h2 := re_dot_le_amgm w u (x - lam) hxl
  rw [hkey] at h2
  have h3 : (x - lam) * ∑ i, Complex.normSq (u i) ≤ (∑ i, Complex.normSq (w i)) / (x - lam) := by
    linarith
  linarith

/-- Spectral bounds for `A = 1 + c Yᴴ (x - c Y Yᴴ)⁻¹ Y` on `{c Y Yᴴ ⪯ lam}`, `0 ≤ lam < x`:
`1 ⪯ A ⪯ x / (x - lam)`. -/
theorem A_bounds {p M : ℕ} (Y : Matrix (Fin p) (Fin M) ℂ) (c x lam : ℝ) (hc : 0 < c)
    (hlam : 0 ≤ lam) (hx : lam < x)
    (hS : ((lam : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (c : ℂ) • (Y * Yᴴ)).PosSemidef) :
    (1 + (c : ℂ) • (Yᴴ * ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (c : ℂ) • (Y * Yᴴ))⁻¹ * Y)).IsHermitian ∧
    (((x / (x - lam) : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) -
      (1 + (c : ℂ) • (Yᴴ * ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (c : ℂ) • (Y * Yᴴ))⁻¹ * Y))).PosSemidef ∧
    (((x / (x - lam) : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) +
      (1 + (c : ℂ) • (Yᴴ * ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (c : ℂ) • (Y * Yᴴ))⁻¹ * Y))).PosSemidef ∧
    ((1 + (c : ℂ) • (Yᴴ * ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (c : ℂ) • (Y * Yᴴ))⁻¹ * Y)) -
      1).PosSemidef := by
  set R := ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (c : ℂ) • (Y * Yᴴ))⁻¹ with hR
  have hsa : ∀ r : ℝ, IsSelfAdjoint (r : ℂ) := fun r => by
    show star (r : ℂ) = r
    simp
  have hSH : ((c : ℂ) • (Y * Yᴴ)).IsHermitian := (isHermitian_mul_conjTranspose_self Y).smul (hsa c)
  have hRH : R.IsHermitian :=
    ((isHermitian_one.smul (hsa x)).sub hSH).inv
  have hAH : (1 + (c : ℂ) • (Yᴴ * R * Y)).IsHermitian :=
    isHermitian_one.add ((isHermitian_conjTranspose_mul_mul Y hRH).smul (hsa c))
  -- the Gram bound c |Y v|² ≤ lam |v|²
  have hgram : ∀ v : Fin M → ℂ, c * ∑ i, Complex.normSq ((Y *ᵥ v) i) ≤ lam * ∑ i, Complex.normSq (v i) := by
    intro v
    set Y' := ((Real.sqrt c : ℝ) : ℂ) • Y with hY'
    have hYY : Y' * Y'ᴴ = (c : ℂ) • (Y * Yᴴ) := by
      rw [hY', conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      rw [show star ((Real.sqrt c : ℝ) : ℂ) = ((Real.sqrt c : ℝ) : ℂ) by simp, ← Complex.ofReal_mul,
        Real.mul_self_sqrt hc.le]
    have hsw := psd_swap Y' lam hlam (by rw [hYY]; exact hS)
    have := (psd_iff_re (isHermitian_smul_one_sub_gram Y' lam)).mp hsw v
    rw [re_quad_sub_gram] at this
    have hY'v : ∀ i, Complex.normSq ((Y' *ᵥ v) i) = c * Complex.normSq ((Y *ᵥ v) i) := fun i => by
      rw [hY', smul_mulVec, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
        Real.mul_self_sqrt hc.le]
    simp only [hY'v, ← Finset.mul_sum] at this
    linarith
  have hquad : ∀ v : Fin M → ℂ, (star v ⬝ᵥ ((1 + (c : ℂ) • (Yᴴ * R * Y)) *ᵥ v)).re =
      ∑ i, Complex.normSq (v i) + c * (star (Y *ᵥ v) ⬝ᵥ (R *ᵥ (Y *ᵥ v))).re := by
    intro v
    rw [add_mulVec, one_mulVec, dotProduct_add, Complex.add_re, re_star_self, smul_mulVec,
      dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, ← star_mulVec]
  have hS' : ((lam : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (c : ℂ) • (Y * Yᴴ)).PosSemidef := hS
  have hRb := fun w => resolvent_quad_bounds ((c : ℂ) • (Y * Yᴴ)) x lam hx hS' w
  have hxl : 0 < x - lam := by linarith
  have hC : x / (x - lam) = 1 + lam / (x - lam) := by field_simp; ring
  refine ⟨hAH, ?_, ?_, ?_⟩
  · rw [psd_iff_re ((isHermitian_one.smul (hsa _)).sub hAH)]
    intro v
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re, re_quad_smul_one, hquad]
    have h1 := (hRb (Y *ᵥ v)).2
    have h2 := hgram v
    have h3 : c * (star (Y *ᵥ v) ⬝ᵥ (R *ᵥ (Y *ᵥ v))).re ≤
        lam / (x - lam) * ∑ i, Complex.normSq (v i) := by
      calc c * (star (Y *ᵥ v) ⬝ᵥ (R *ᵥ (Y *ᵥ v))).re
          ≤ c * ((∑ i, Complex.normSq ((Y *ᵥ v) i)) / (x - lam)) :=
            mul_le_mul_of_nonneg_left h1 hc.le
        _ = (c * ∑ i, Complex.normSq ((Y *ᵥ v) i)) / (x - lam) := by ring
        _ ≤ (lam * ∑ i, Complex.normSq (v i)) / (x - lam) :=
            div_le_div_of_nonneg_right h2 hxl.le
        _ = lam / (x - lam) * ∑ i, Complex.normSq (v i) := by ring
    rw [hC]
    linarith
  · rw [psd_iff_re ((isHermitian_one.smul (hsa _)).add hAH)]
    intro v
    rw [add_mulVec, dotProduct_add, Complex.add_re, re_quad_smul_one, hquad]
    have h1 := (hRb (Y *ᵥ v)).1
    have hv0 : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hC0 : 0 ≤ x / (x - lam) := div_nonneg (by linarith) hxl.le
    have := mul_nonneg hc.le h1
    have := mul_nonneg hC0 hv0
    linarith
  · rw [psd_iff_re (hAH.sub isHermitian_one)]
    intro v
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re, hquad, one_mulVec, re_star_self]
    have h1 := (hRb (Y *ᵥ v)).1
    have := mul_nonneg hc.le h1
    linarith

end

-- ===== from BlockForm.lean =====
section

/-- `λ₁ ≤ x` iff every eigenvalue of `S` is `≤ x` (for `N ≥ 1`). -/
theorem largestEig_le_iff (M : ℕ) {N : ℕ} [NeZero N] (U : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) (x : ℝ) :
    largestEig M U ℓ G ≤ x ↔ ∀ i, (sampleCov_isHermitian M U ℓ G).eigenvalues i ≤ x := by
  unfold largestEig
  exact ciSup_le_iff (Set.finite_range _).bddAbove

/-- The data matrix `Y = D^{1/2} Gᵀ` (rows = coordinates, columns = samples). -/
noncomputable def dataMat (M : ℕ) {N : ℕ} (ℓ : Fin N → ℝ) (G : Fin M → Fin N → ℂ) :
    Matrix (Fin N) (Fin M) ℂ :=
  Matrix.of fun j k => (Real.sqrt (ℓ j) : ℂ) * G k j

/-- `S(1) = M⁻¹ Y Yᴴ`. -/
theorem sampleCov_one_eq (M : ℕ) {N : ℕ} (ℓ : Fin N → ℝ) (G : Fin M → Fin N → ℂ) :
    sampleCov M 1 ℓ G = (M : ℂ)⁻¹ • (dataMat M ℓ G * (dataMat M ℓ G)ᴴ) := by
  ext i j
  simp [sampleCov, sampleVec, dataMat, Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply,
    Matrix.one_mulVec]

section Blocks
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Rows of `Y` in the spike part `m` / null part `n` of a splitting `e : Fin N ≃ m ⊕ n`. -/
def upperRows {N M : ℕ} (e : Fin N ≃ m ⊕ n) (Y : Matrix (Fin N) (Fin M) ℂ) : Matrix m (Fin M) ℂ :=
  Matrix.of fun a k => Y (e.symm (Sum.inl a)) k

def lowerRows {N M : ℕ} (e : Fin N ≃ m ⊕ n) (Y : Matrix (Fin N) (Fin M) ℂ) : Matrix n (Fin M) ℂ :=
  Matrix.of fun a k => Y (e.symm (Sum.inr a)) k

theorem reindex_toBlocks₁₁ {N M : ℕ} (c : ℂ) (e : Fin N ≃ m ⊕ n) (Y : Matrix (Fin N) (Fin M) ℂ) :
    (reindex e e (c • (Y * Yᴴ))).toBlocks₁₁ = c • (upperRows e Y * (upperRows e Y)ᴴ) := by
  ext i j; simp [toBlocks₁₁, upperRows, Matrix.mul_apply]

theorem reindex_toBlocks₁₂ {N M : ℕ} (c : ℂ) (e : Fin N ≃ m ⊕ n) (Y : Matrix (Fin N) (Fin M) ℂ) :
    (reindex e e (c • (Y * Yᴴ))).toBlocks₁₂ = c • (upperRows e Y * (lowerRows e Y)ᴴ) := by
  ext i j; simp [toBlocks₁₂, upperRows, lowerRows, Matrix.mul_apply]

theorem reindex_toBlocks₂₂ {N M : ℕ} (c : ℂ) (e : Fin N ≃ m ⊕ n) (Y : Matrix (Fin N) (Fin M) ℂ) :
    (reindex e e (c • (Y * Yᴴ))).toBlocks₂₂ = c • (lowerRows e Y * (lowerRows e Y)ᴴ) := by
  ext i j; simp [toBlocks₂₂, lowerRows, Matrix.mul_apply]

/-- The Schur matrix factors through the spike rows: `K = c Y₁ (1 + c Y₂ᴴ R Y₂) Y₁ᴴ`. -/
theorem schurK_eq {M : ℕ} (c : ℂ) (hc : star c = c) (Y1 : Matrix m (Fin M) ℂ)
    (Y2 : Matrix n (Fin M) ℂ) (R : Matrix n n ℂ) :
    c • (Y1 * Y1ᴴ) + c • (Y1 * Y2ᴴ) * R * (c • (Y1 * Y2ᴴ))ᴴ =
      c • (Y1 * (1 + c • (Y2ᴴ * R * Y2)) * Y1ᴴ) := by
  rw [conjTranspose_smul, hc, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, smul_smul, Matrix.mul_assoc]

end Blocks

end

-- ===== from SchurEig.lean =====
section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem isHermitian_smul_one_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) :
    ((x : ℂ) • (1 : Matrix n n ℂ) - A).IsHermitian := by
  refine IsHermitian.sub ?_ hA
  simp [IsHermitian, conjTranspose_smul]

/-- The eigenvalues of `x - A` are the `x - λ_j(A)`, as a statement about any property. -/
theorem forall_eig_smul_one_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) (P : ℝ → Prop) :
    (∀ i, P ((isHermitian_smul_one_sub hA x).eigenvalues i)) ↔ ∀ j, P (x - hA.eigenvalues j) := by
  set hH := isHermitian_smul_one_sub hA x
  have hs : spectrum ℂ ((x : ℂ) • (1 : Matrix n n ℂ) - A) = ({(x : ℂ)} : Set ℂ) - spectrum ℂ A := by
    rw [← Algebra.algebraMap_eq_smul_one, spectrum.singleton_sub_eq]
  rw [hH.spectrum_eq_image_range, hA.spectrum_eq_image_range] at hs
  constructor
  · intro h j
    have hmem : ((x - hA.eigenvalues j : ℝ) : ℂ) ∈ (RCLike.ofReal '' Set.range hH.eigenvalues : Set ℂ) := by
      rw [hs]
      exact Set.mem_sub.mpr ⟨x, rfl, _, ⟨_, ⟨j, rfl⟩, rfl⟩, by push_cast; rfl⟩
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hmem
    have : hH.eigenvalues i = x - hA.eigenvalues j := RCLike.ofReal_injective hi
    rw [← this]; exact h i
  · intro h i
    have hmem : ((hH.eigenvalues i : ℝ) : ℂ) ∈ ({(x : ℂ)} - RCLike.ofReal '' Set.range hA.eigenvalues : Set ℂ) := by
      rw [← hs]; exact ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨y, hy, z, ⟨_, ⟨j, rfl⟩, rfl⟩, hyz⟩ := Set.mem_sub.mp hmem
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have : hH.eigenvalues i = x - hA.eigenvalues j := by
      have h2 : ((x - hA.eigenvalues j : ℝ) : ℂ) = ((hH.eigenvalues i : ℝ) : ℂ) := by
        rw [← hyz]; push_cast; rfl
      exact_mod_cast h2.symm
    rw [this]; exact h j

theorem eig_le_iff_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) :
    (∀ j, hA.eigenvalues j ≤ x) ↔ ((x : ℂ) • (1 : Matrix n n ℂ) - A).PosSemidef := by
  rw [(isHermitian_smul_one_sub hA x).posSemidef_iff_eigenvalues_nonneg, Pi.le_def]
  simp only [Pi.zero_apply]
  rw [forall_eig_smul_one_sub hA x (fun t => 0 ≤ t)]
  simp only [sub_nonneg]

theorem eig_lt_iff_posDef {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) :
    (∀ j, hA.eigenvalues j < x) ↔ ((x : ℂ) • (1 : Matrix n n ℂ) - A).PosDef := by
  rw [(isHermitian_smul_one_sub hA x).posDef_iff_eigenvalues_pos]
  rw [forall_eig_smul_one_sub hA x (fun t => 0 < t)]
  simp only [sub_pos]

/-- P5 core (deterministic): for `x` above the spectrum of the null block `D`, every eigenvalue of
`[[A, B], [Bᴴ, D]]` is `≤ x` iff every eigenvalue of the `m × m` matrix `A + B (x - D)⁻¹ Bᴴ` is `≤ x`. -/
theorem eig_fromBlocks_le_iff (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hD : D.IsHermitian) (hS : (fromBlocks A B Bᴴ D).IsHermitian) (x : ℝ)
    (hK : (A + B * ((x : ℂ) • (1 : Matrix n n ℂ) - D)⁻¹ * Bᴴ).IsHermitian)
    (hx : ∀ j, hD.eigenvalues j < x) :
    (∀ i, hS.eigenvalues i ≤ x) ↔ (∀ i, hK.eigenvalues i ≤ x) := by
  rw [eig_le_iff_posSemidef, eig_le_iff_posSemidef]
  have hPD := (eig_lt_iff_posDef hD x).mp hx
  let _ : Invertible ((x : ℂ) • (1 : Matrix n n ℂ) - D) := invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit)
  have hblk : (x : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) - fromBlocks A B Bᴴ D =
      fromBlocks ((x : ℂ) • 1 - A) (-B) (-B)ᴴ ((x : ℂ) • 1 - D) := by
    ext (i | i) (j | j) <;> simp [fromBlocks, Matrix.one_apply]
  rw [hblk, Matrix.PosDef.fromBlocks₂₂ _ _ hPD]
  have : (x : ℂ) • (1 : Matrix m m ℂ) - A - -B * ((x : ℂ) • 1 - D)⁻¹ * (-B)ᴴ =
      (x : ℂ) • (1 : Matrix m m ℂ) - (A + B * ((x : ℂ) • 1 - D)⁻¹ * Bᴴ) := by
    simp [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, sub_sub]
  rw [this]

/-- Reindexing does not change the set of eigenvalues. -/
theorem range_eig_reindex {n' : Type*} [Fintype n'] [DecidableEq n'] (e : n ≃ n')
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n' n' ℂ) (hB : B.IsHermitian)
    (heq : B = reindex e e A) :
    Set.range hB.eigenvalues = Set.range hA.eigenvalues := by
  have hs : spectrum ℂ B = spectrum ℂ A := by
    rw [heq]
    have := AlgEquiv.spectrum_eq (reindexAlgEquiv ℂ ℂ e) A
    simpa using this
  rw [hB.spectrum_eq_image_range, hA.spectrum_eq_image_range] at hs
  exact (Set.image_injective.mpr RCLike.ofReal_injective) hs

theorem forall_eig_reindex {n' : Type*} [Fintype n'] [DecidableEq n'] (e : n ≃ n')
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n' n' ℂ) (hB : B.IsHermitian)
    (heq : B = reindex e e A) (P : ℝ → Prop) :
    (∀ i, P (hB.eigenvalues i)) ↔ ∀ i, P (hA.eigenvalues i) := by
  have h := range_eig_reindex e hA B hB heq
  constructor
  · intro hP i
    obtain ⟨j, hj⟩ : hA.eigenvalues i ∈ Set.range hB.eigenvalues := h ▸ ⟨i, rfl⟩
    rw [← hj]; exact hP j
  · intro hP i
    obtain ⟨j, hj⟩ : hB.eigenvalues i ∈ Set.range hA.eigenvalues := h ▸ ⟨i, rfl⟩
    rw [← hj]; exact hP j

/-- P5 core in block coordinates: split the index set of a Hermitian `S` by `e : n' ≃ m ⊕ n`
(spike part `m`, null part `n`); if `x` exceeds every eigenvalue of the null block `D`, then
`λ_max(S) ≤ x` iff `λ_max(A + B (x - D)⁻¹ Bᴴ) ≤ x`. -/
theorem eig_le_iff_schur_blocks {n' : Type*} [Fintype n'] [DecidableEq n'] {S : Matrix n' n' ℂ}
    (hS : S.IsHermitian) (e : n' ≃ m ⊕ n) (x : ℝ)
    (hD : (reindex e e S).toBlocks₂₂.IsHermitian)
    (hK : ((reindex e e S).toBlocks₁₁ + (reindex e e S).toBlocks₁₂ *
      ((x : ℂ) • (1 : Matrix n n ℂ) - (reindex e e S).toBlocks₂₂)⁻¹ *
        ((reindex e e S).toBlocks₁₂)ᴴ).IsHermitian)
    (hx : ∀ j, hD.eigenvalues j < x) :
    (∀ i, hS.eigenvalues i ≤ x) ↔ ∀ i, hK.eigenvalues i ≤ x := by
  set S' := reindex e e S with hS'def
  have hS' : S'.IsHermitian := by rw [hS'def, reindex_apply]; exact hS.submatrix _
  have h21 : S'.toBlocks₂₁ = S'.toBlocks₁₂ᴴ := by
    ext i j
    simp only [toBlocks₂₁, toBlocks₁₂, conjTranspose_apply, of_apply]
    exact (hS'.apply _ _).symm
  have hfb : fromBlocks S'.toBlocks₁₁ S'.toBlocks₁₂ S'.toBlocks₁₂ᴴ S'.toBlocks₂₂ = S' := by
    rw [← h21, fromBlocks_toBlocks]
  have hS'' : (fromBlocks S'.toBlocks₁₁ S'.toBlocks₁₂ S'.toBlocks₁₂ᴴ S'.toBlocks₂₂).IsHermitian :=
    hfb ▸ hS'
  rw [← eig_fromBlocks_le_iff _ _ _ hD hS'' x hK hx]
  exact (forall_eig_reindex e hS _ hS'' hfb (fun t => t ≤ x)).symm

end

-- ===== from Identities.lean =====
section

/-- `γ⁻² = N/M` for `γ = √(M/N)`. -/
theorem gamma_inv_sq (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    (Real.sqrt ((M : ℝ) / N))⁻¹ ^ 2 = (N : ℝ) / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- At `ψ = 1/L` the inverse companion Stieltjes map `x(ψ) = 1/ψ + y/(1-ψ)` is the BBP centre
`ρ = L + L y/(L-1)`. -/
theorem rho_psi (L y : ℝ) (hL : 1 < L) : 1 / (1 / L) + y / (1 - 1 / L) = L + L * y / (L - 1) := by
  have h1 : L - 1 ≠ 0 := by linarith
  have h0 : L ≠ 0 := by linarith
  field_simp

/-- `-1/x'(ψ)` at `ψ = 1/L` is `1/σ²` with `σ² = L² - L² y/(L-1)²` (the BBP variance). -/
theorem sigma_psi (L y : ℝ) (hL : 1 < L) :
    (1 / L)⁻¹ ^ 2 - y / (1 - 1 / L) ^ 2 = L ^ 2 - L ^ 2 * y / (L - 1) ^ 2 := by
  have h1 : L - 1 ≠ 0 := by linarith
  have h0 : L ≠ 0 := by linarith
  field_simp

/-- The BBP centre is right of the bulk edge with a uniform gap:
`ρ - (1+√y)² = (L-1-√y)²/(L-1)`. -/
theorem rho_sub_edge (L y : ℝ) (hL : 1 < L) (hy : 0 ≤ y) :
    L + L * y / (L - 1) - (1 + Real.sqrt y) ^ 2 = (L - 1 - Real.sqrt y) ^ 2 / (L - 1) := by
  have h1 : L - 1 ≠ 0 := by linarith
  have hs := Real.sq_sqrt hy
  field_simp
  nlinarith [hs]

end

-- ===== from Uniform.lean =====
section

/-- Conditioning glue: if `h n` (a conditional probability, values in `[0,1]`) converges to `c`
along EVERY sequence of points that are eventually in the good sets, and the good sets have
probability tending to `1`, then `∫ h n → c`. -/
theorem integral_tendsto_of_pointwise {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] (h : ∀ n, Ω n → ℝ)
    (hm : ∀ n, Measurable (h n)) (h01 : ∀ n ω, 0 ≤ h n ω ∧ h n ω ≤ 1)
    (Good : ∀ n, Set (Ω n)) (hGm : ∀ n, MeasurableSet (Good n))
    (hGood : Tendsto (fun n => (P n).real (Good n)ᶜ) atTop (𝓝 0)) (c : ℝ)
    (hpt : ∀ ω : ∀ n, Ω n, (∀ᶠ n in atTop, ω n ∈ Good n) →
      Tendsto (fun n => h n (ω n)) atTop (𝓝 c)) :
    Tendsto (fun n => ∫ x, h n x ∂P n) atTop (𝓝 c) := by
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  set B : ℝ := 1 + |c| with hB
  have hBpos : 0 < B := by positivity
  have hne : ∀ n, Nonempty (Ω n) := by
    intro n
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := measure_univ (μ := P n)
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at h1
    exact zero_ne_one h1
  -- eventually the bad set has small probability
  have hsmall : ∀ᶠ n in atTop, (P n).real (Good n)ᶜ < min (ε / (2 * B)) 1 :=
    (tendsto_order.1 hGood).2 _ (lt_min (by positivity) one_pos)
  let bad : ℕ → Prop := fun n => ∃ ω ∈ Good n, ε / 2 ≤ |h n ω - c|
  have hbad : ∀ n, (P n).real (Good n)ᶜ < ε / (2 * B) → ε ≤ dist (∫ x, h n x ∂P n) c → bad n := by
    intro n hn hd
    by_contra hnb
    simp only [bad, not_exists, not_and, not_le] at hnb
    have hint : Integrable (h n) (P n) := by
      refine Integrable.of_bound (C := 1) (hm n).aestronglyMeasurable (Filter.Eventually.of_forall
        fun ω => ?_)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(h01 n ω).1, (h01 n ω).2]
    have hpoint : ∀ ω, |h n ω - c| ≤ ε / 2 + B * (Good n)ᶜ.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases hω : ω ∈ Good n
      · have := (hnb ω hω).le
        rw [Set.indicator_of_notMem (by simpa using hω)]; linarith
      · rw [Set.indicator_of_mem (by simpa using hω), mul_one]
        have : |h n ω - c| ≤ |h n ω| + |c| := abs_sub _ _
        rw [abs_of_nonneg (h01 n ω).1] at this
        linarith [(h01 n ω).2, half_pos hε]
    have hind : Integrable ((Good n)ᶜ.indicator (fun _ => (1 : ℝ))) (P n) :=
      (integrable_const (1 : ℝ)).indicator (hGm n).compl
    have hle : |∫ x, h n x ∂P n - c| ≤ ε / 2 + B * (P n).real (Good n)ᶜ := by
      have e1 : ∫ x, h n x ∂P n - c = ∫ x, (h n x - c) ∂P n := by
        rw [integral_sub hint (integrable_const c), integral_const, probReal_univ, one_smul]
      rw [e1]
      calc |∫ x, (h n x - c) ∂P n| ≤ ∫ x, |h n x - c| ∂P n := abs_integral_le_integral_abs
        _ ≤ ∫ x, (ε / 2 + B * (Good n)ᶜ.indicator (fun _ => (1 : ℝ)) x) ∂P n := by
            refine integral_mono (hint.sub (integrable_const c)).abs ?_ hpoint
            exact (integrable_const _).add (hind.const_mul B)
        _ = ε / 2 + B * (P n).real (Good n)ᶜ := by
            rw [integral_add (integrable_const _) (hind.const_mul B), integral_const, probReal_univ,
              one_smul, integral_const_mul, integral_indicator_const _ (hGm n).compl, smul_eq_mul, mul_one]
    have : B * (P n).real (Good n)ᶜ < ε / 2 := by
      calc B * (P n).real (Good n)ᶜ < B * (ε / (2 * B)) := mul_lt_mul_of_pos_left hn hBpos
        _ = ε / 2 := by field_simp
    rw [Real.dist_eq] at hd
    linarith
  -- build the sequence
  classical
  let ω : ∀ n, Ω n := fun n =>
    if hb : bad n then hb.choose
    else if hg : (Good n).Nonempty then hg.some else (hne n).some
  have hωgood : ∀ᶠ n in atTop, ω n ∈ Good n := by
    filter_upwards [hsmall] with n hn
    have hg : (Good n).Nonempty := by
      by_contra hg
      rw [Set.not_nonempty_iff_eq_empty] at hg
      rw [hg, Set.compl_empty, probReal_univ] at hn
      exact (lt_irrefl _ (lt_of_lt_of_le hn (min_le_right _ _)))
    simp only [ω]
    split_ifs with hb
    · exact hb.choose_spec.1
    · exact hg.some_mem
  have hlim := hpt ω hωgood
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N1, hN1⟩ := hlim (ε / 2) (half_pos hε)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hsmall
  obtain ⟨n, hn, hd⟩ := hfreq (max N1 N2)
  have hb : bad n := hbad n (lt_of_lt_of_le (hN2 n (le_of_max_le_right hn)) (min_le_left _ _)) hd
  have h1 := hN1 n (le_of_max_le_left hn)
  have h2 : ε / 2 ≤ |h n (ω n) - c| := by
    simp only [ω, dif_pos hb]
    exact hb.choose_spec.2
  rw [Real.dist_eq] at h1
  linarith

end

-- ===== from Assembly1.lean =====
section

/-- Events `t - F ⪰ 0` are measurable for measurable Hermitian-valued `F` (via `phi`). -/
theorem measurableSet_psd {α : Type*} [MeasurableSpace α] {k : ℕ} (F : α → (Fin k → Fin k → ℂ))
    (hF : Measurable F) (hH : ∀ a, (Matrix.of (F a)).IsHermitian) (t : ℝ) :
    MeasurableSet {a | ((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - Matrix.of (F a)).PosSemidef} := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    convert MeasurableSet.univ
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have h0 : ((t : ℂ) • (1 : Matrix (Fin 0) (Fin 0) ℂ) - Matrix.of (F a)) = 0 := by
      ext i; exact i.elim0
    rw [h0]; exact PosSemidef.zero
  · have hset : {a | ((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - Matrix.of (F a)).PosSemidef} =
        {a | phi (F a) ≤ t} := by
      ext a
      simp only [Set.mem_setOf_eq]
      rw [phi_le_iff hk, herm_of_isHermitian _ (hH a)]
    rw [hset]
    exact measurableSet_le (continuous_phi.measurable.comp hF) measurable_const

/-- Section identity (Schur complement once): on `{λ_max(S₂₂) ≤ lam < x}`, `λ₁ ≤ x` iff the
`r × r` spike block `x - M⁻¹ Δ Y₁ A Y₁ᴴ Δ` is PSD, `A = 1 + M⁻¹ Y₂ᴴ (x - M⁻¹ Y₂Y₂ᴴ)⁻¹ Y₂`. -/
theorem section_iff {M N r p : ℕ} [NeZero N] (e : Fin N ≃ Fin r ⊕ Fin p) (ℓ : Fin N → ℝ)
    (hnull : ∀ b, ℓ (e.symm (Sum.inr b)) = 1) (X : Fin M → Fin N → ℂ) (x lam : ℝ) (hx : lam < x)
    (hS : ((lam : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ •
      ((Matrix.of (fun k b => X k (e.symm (Sum.inr b))))ᵀ *
        ((Matrix.of (fun k b => X k (e.symm (Sum.inr b))))ᵀ)ᴴ)).PosSemidef) :
    largestEig M 1 ℓ X ≤ x ↔
      ((x : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
        (M : ℂ)⁻¹ • (diagonal (fun a => (Real.sqrt (ℓ (e.symm (Sum.inl a))) : ℂ)) *
          (Matrix.of (fun k a => X k (e.symm (Sum.inl a))))ᵀ *
          (1 + (M : ℂ)⁻¹ • (((Matrix.of (fun k b => X k (e.symm (Sum.inr b))))ᵀ)ᴴ *
            ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ •
              ((Matrix.of (fun k b => X k (e.symm (Sum.inr b))))ᵀ *
                ((Matrix.of (fun k b => X k (e.symm (Sum.inr b))))ᵀ)ᴴ))⁻¹ *
            (Matrix.of (fun k b => X k (e.symm (Sum.inr b))))ᵀ)) *
          ((Matrix.of (fun k a => X k (e.symm (Sum.inl a))))ᵀ)ᴴ *
          diagonal (fun a => (Real.sqrt (ℓ (e.symm (Sum.inl a))) : ℂ)))).PosSemidef := by
  set Y2 := (Matrix.of (fun k b => X k (e.symm (Sum.inr b))))ᵀ with hY2
  set Y1 := (Matrix.of (fun k a => X k (e.symm (Sum.inl a))))ᵀ with hY1
  set Δ := diagonal (fun a => (Real.sqrt (ℓ (e.symm (Sum.inl a))) : ℂ)) with hΔ
  have hS' := sampleCov_one_eq M ℓ X
  have hlow : lowerRows e (dataMat M ℓ X) = Y2 := by
    ext b k; simp [lowerRows, dataMat, hnull, hY2]
  have hup : upperRows e (dataMat M ℓ X) = Δ * Y1 := by
    ext a k; simp [upperRows, dataMat, hΔ, hY1, diagonal_mul]
  have hc : star ((M : ℂ)⁻¹) = (M : ℂ)⁻¹ := by simp
  have h11 : (reindex e e (sampleCov M 1 ℓ X)).toBlocks₁₁ = (M : ℂ)⁻¹ • ((Δ * Y1) * (Δ * Y1)ᴴ) := by
    rw [hS', reindex_toBlocks₁₁, hup]
  have h12 : (reindex e e (sampleCov M 1 ℓ X)).toBlocks₁₂ = (M : ℂ)⁻¹ • ((Δ * Y1) * Y2ᴴ) := by
    rw [hS', reindex_toBlocks₁₂, hup, hlow]
  have h22 : (reindex e e (sampleCov M 1 ℓ X)).toBlocks₂₂ = (M : ℂ)⁻¹ • (Y2 * Y2ᴴ) := by
    rw [hS', reindex_toBlocks₂₂, hlow]
  have hsa : IsSelfAdjoint ((M : ℂ)⁻¹) := by simp [IsSelfAdjoint]
  have hD : (reindex e e (sampleCov M 1 ℓ X)).toBlocks₂₂.IsHermitian := by
    rw [h22]; exact (isHermitian_mul_conjTranspose_self Y2).smul hsa
  have hR : (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
      (reindex e e (sampleCov M 1 ℓ X)).toBlocks₂₂)⁻¹).IsHermitian :=
    (isHermitian_smul_one_sub hD x).inv
  have hK : ((reindex e e (sampleCov M 1 ℓ X)).toBlocks₁₁ + (reindex e e (sampleCov M 1 ℓ X)).toBlocks₁₂ *
      ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (reindex e e (sampleCov M 1 ℓ X)).toBlocks₂₂)⁻¹ *
        ((reindex e e (sampleCov M 1 ℓ X)).toBlocks₁₂)ᴴ).IsHermitian := by
    refine IsHermitian.add ?_ (isHermitian_mul_mul_conjTranspose _ hR)
    rw [h11]; exact (isHermitian_mul_conjTranspose_self _).smul hsa
  have hlam : ∀ j, hD.eigenvalues j ≤ lam := by
    rw [eig_le_iff_posSemidef hD lam, h22]; exact hS
  have hx' : ∀ j, hD.eigenvalues j < x := fun j => lt_of_le_of_lt (hlam j) hx
  rw [largestEig_le_iff, eig_le_iff_schur_blocks (sampleCov_isHermitian M 1 ℓ X) e x hD hK hx',
    eig_le_iff_posSemidef hK x, h11, h12, h22, schurK_eq _ hc]
  have hΔH : Δᴴ = Δ := by
    rw [hΔ, diagonal_conjTranspose]; congr 1; funext a; simp
  rw [conjTranspose_mul, hΔH]
  simp only [Matrix.mul_assoc]

/-- Deterministic asymptotics of the companion Stieltjes parameter: `x_n = ρ_n + t σ_n/√M`,
`ψ_n` the small root of `x ψ² - (x+1-y) ψ + 1 = 0`. -/
theorem psi_asymp (L y : ℕ → ℝ) (L0 y0 : ℝ) (hL : Tendsto L atTop (𝓝 L0))
    (hy : Tendsto y atTop (𝓝 y0)) (hy0 : 0 ≤ y0) (hgap : 1 + Real.sqrt y0 < L0)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (t : ℝ) (x ψ : ℕ → ℝ)
    (hx : ∀ n, x n = L n + L n * y n / (L n - 1) +
      t * Real.sqrt (L n ^ 2 - L n ^ 2 * y n / (L n - 1) ^ 2) / Real.sqrt (M n))
    (hψ : ∀ n, ψ n = ((x n + 1 - y n) - Real.sqrt ((x n + 1 - y n) ^ 2 - 4 * x n)) / (2 * x n)) :
    Tendsto ψ atTop (𝓝 (1 / L0)) ∧ (∀ᶠ n in atTop, 1 / ψ n + y n / (1 - ψ n) = x n) ∧
    Tendsto x atTop (𝓝 (L0 + L0 * y0 / (L0 - 1))) ∧
    Tendsto (fun n => Real.sqrt (M n) * x n * (1 - L n * ψ n)) atTop
      (𝓝 (L0 * (L0 + L0 * y0 / (L0 - 1)) * t / Real.sqrt (L0 ^ 2 - L0 ^ 2 * y0 / (L0 - 1) ^ 2))) ∧
    Tendsto (fun n => x n ^ 2 / ((ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2)) atTop
      (𝓝 ((L0 + L0 * y0 / (L0 - 1)) ^ 2 / (L0 ^ 2 - L0 ^ 2 * y0 / (L0 - 1) ^ 2))) := by
  have hL1 : 1 < L0 := by linarith only [hgap, Real.sqrt_nonneg y0]
  have hL0 : 0 < L0 := by linarith only [hL1]
  have hL0m : 0 < L0 - 1 := by linarith only [hL1]
  have hy0lt : y0 < (L0 - 1) ^ 2 := by
    nlinarith only [Real.sq_sqrt hy0, Real.sqrt_nonneg y0, hgap]
  have hσ0sq : 0 < L0 ^ 2 - L0 ^ 2 * y0 / (L0 - 1) ^ 2 := by
    have h1 : y0 / (L0 - 1) ^ 2 < 1 := by rw [div_lt_one (pow_pos hL0m 2)]; exact hy0lt
    have h2 : L0 ^ 2 * y0 / (L0 - 1) ^ 2 = L0 ^ 2 * (y0 / (L0 - 1) ^ 2) := by ring
    rw [h2]; have h3 := mul_pos (pow_pos hL0 2) (sub_pos.mpr h1); linarith only [h3]
  set ρ0 := L0 + L0 * y0 / (L0 - 1) with hρ0
  set σ0 := Real.sqrt (L0 ^ 2 - L0 ^ 2 * y0 / (L0 - 1) ^ 2) with hσ0
  have hσ0pos : 0 < σ0 := Real.sqrt_pos.mpr hσ0sq
  have hρ0pos : 0 < ρ0 := by
    have : 0 ≤ L0 * y0 / (L0 - 1) := div_nonneg (mul_nonneg hL0.le hy0) hL0m.le
    linarith only [this, hL0, hρ0]
  have hLm1 : Tendsto (fun n => L n - 1) atTop (𝓝 (L0 - 1)) := hL.sub_const 1
  have hρ : Tendsto (fun n => L n + L n * y n / (L n - 1)) atTop (𝓝 ρ0) :=
    hL.add ((hL.mul hy).div hLm1 hL0m.ne')
  have hσ : Tendsto (fun n => Real.sqrt (L n ^ 2 - L n ^ 2 * y n / (L n - 1) ^ 2)) atTop (𝓝 σ0) :=
    ((hL.pow 2).sub (((hL.pow 2).mul hy).div (hLm1.pow 2) (by positivity))).sqrt
  have hMr : Tendsto (fun n => (M n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hM
  have hsM : Tendsto (fun n => (Real.sqrt (M n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hMr)
  have hxl : Tendsto x atTop (𝓝 ρ0) := by
    have h := hρ.add (((tendsto_const_nhds (x := t)).mul hσ).mul hsM)
    rw [mul_zero, add_zero] at h
    exact h.congr (fun n => by rw [hx n]; ring)
  have hB0 : ρ0 + 1 - y0 = ρ0 / L0 + L0 := by
    rw [hρ0]; field_simp; ring
  have hgt : 0 < L0 - ρ0 / L0 := by
    rw [sub_pos, div_lt_iff₀ hL0, hρ0]
    have : L0 * y0 / (L0 - 1) < L0 * (L0 - 1) := by
      rw [div_lt_iff₀ hL0m]; linarith only [mul_lt_mul_of_pos_left hy0lt hL0]
    linarith only [this]
  have hdisc0 : (ρ0 + 1 - y0) ^ 2 - 4 * ρ0 = (L0 - ρ0 / L0) ^ 2 := by
    rw [hB0]; field_simp; ring
  have hψ0 : ((ρ0 + 1 - y0) - Real.sqrt ((ρ0 + 1 - y0) ^ 2 - 4 * ρ0)) / (2 * ρ0) = 1 / L0 := by
    rw [hdisc0, Real.sqrt_sq hgt.le, hB0]; field_simp; ring
  have hB : Tendsto (fun n => x n + 1 - y n) atTop (𝓝 (ρ0 + 1 - y0)) := (hxl.add_const 1).sub hy
  have hdl : Tendsto (fun n => (x n + 1 - y n) ^ 2 - 4 * x n) atTop
      (𝓝 ((ρ0 + 1 - y0) ^ 2 - 4 * ρ0)) := (hB.pow 2).sub (hxl.const_mul 4)
  have hψl : Tendsto ψ atTop (𝓝 (1 / L0)) := by
    rw [← hψ0]
    exact ((hB.sub hdl.sqrt).div (hxl.const_mul 2) (by positivity)).congr (fun n => (hψ n).symm)
  have hdpos : 0 < (ρ0 + 1 - y0) ^ 2 - 4 * ρ0 := by rw [hdisc0]; positivity
  have ev1 : ∀ᶠ n in atTop, 0 < x n := hxl.eventually (eventually_gt_nhds hρ0pos)
  have ev2 : ∀ᶠ n in atTop, 0 < (x n + 1 - y n) ^ 2 - 4 * x n :=
    hdl.eventually (eventually_gt_nhds hdpos)
  have ev3 : ∀ᶠ n in atTop, 0 < ψ n := hψl.eventually (eventually_gt_nhds (by positivity))
  have ev4 : ∀ᶠ n in atTop, ψ n < 1 :=
    hψl.eventually (eventually_lt_nhds (by rw [div_lt_one hL0]; exact hL1))
  have hsol : ∀ᶠ n in atTop, 1 / ψ n + y n / (1 - ψ n) = x n := by
    filter_upwards [ev1, ev2, ev3, ev4] with n h1 h2 h3 h4
    have hs := Real.sq_sqrt h2.le
    have hq : x n * ψ n ^ 2 - (x n + 1 - y n) * ψ n + 1 = 0 := by
      have : x n * ψ n ^ 2 - (x n + 1 - y n) * ψ n + 1 =
          ((Real.sqrt ((x n + 1 - y n) ^ 2 - 4 * x n)) ^ 2 - ((x n + 1 - y n) ^ 2 - 4 * x n)) /
            (4 * x n) := by
        rw [hψ n]; field_simp; ring
      rw [this, hs, sub_self, zero_div]
    have h1ψ : 1 - ψ n ≠ 0 := sub_ne_zero.mpr h4.ne'
    rw [div_add_div _ _ h3.ne' h1ψ, div_eq_iff (mul_ne_zero h3.ne' h1ψ)]
    linear_combination hq
  refine ⟨hψl, hsol, hxl, ?_, ?_⟩
  · -- D_n → -σ0²
    have hD : Tendsto (fun n => -L n / ψ n + y n / ((1 - ψ n) * (1 - 1 / L n))) atTop
        (𝓝 (-L0 / (1 / L0) + y0 / ((1 - 1 / L0) * (1 - 1 / L0)))) := by
      refine (hL.neg.div hψl (by positivity)).add (hy.div ((tendsto_const_nhds.sub hψl).mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.div hL hL0.ne'))) ?_)
      have : 1 - 1 / L0 ≠ 0 := by rw [sub_ne_zero]; intro h; rw [eq_div_iff hL0.ne'] at h; linarith only [h, hL1]
      exact mul_ne_zero this this
    have hD0 : -L0 / (1 / L0) + y0 / ((1 - 1 / L0) * (1 - 1 / L0)) = -σ0 ^ 2 := by
      rw [hσ0, Real.sq_sqrt hσ0sq.le]; field_simp; ring
    rw [hD0] at hD
    have hlim := (((hL.neg.mul hxl).mul (tendsto_const_nhds (x := t))).mul hσ).div hD
      (neg_ne_zero.mpr (pow_pos hσ0pos 2).ne')
    have hval : -L0 * ρ0 * t * σ0 / -σ0 ^ 2 = L0 * ρ0 * t / σ0 := by
      field_simp
    rw [hval] at hlim
    refine hlim.congr' ?_
    have ev5 : ∀ᶠ n in atTop, 1 < L n := hL.eventually (eventually_gt_nhds hL1)
    have ev6 : ∀ᶠ n in atTop, -L n / ψ n + y n / ((1 - ψ n) * (1 - 1 / L n)) ≠ 0 :=
      hD.eventually (eventually_ne_nhds (neg_ne_zero.mpr (pow_pos hσ0pos 2).ne'))
    have ev7 : ∀ᶠ n in atTop, 1 ≤ M n := hM.eventually (eventually_ge_atTop 1)
    filter_upwards [hsol, ev3, ev4, ev5, ev6, ev7] with n h1 h3 h4 h5 h6 h7
    set Dn := -L n / ψ n + y n / ((1 - ψ n) * (1 - 1 / L n)) with hDn
    have hLn0 : L n ≠ 0 := (by linarith only [h5] : (0:ℝ) < L n).ne'
    have hL1n : L n - 1 ≠ 0 := (sub_pos.mpr h5).ne'
    have h1ψ : 1 - ψ n ≠ 0 := sub_ne_zero.mpr h4.ne'
    have hsMpos : 0 < Real.sqrt (M n) := Real.sqrt_pos.mpr (by exact_mod_cast h7)
    have hxid : x n - (L n + L n * y n / (L n - 1)) = (ψ n - 1 / L n) * Dn := by
      rw [← h1, ← rho_psi (L n) (y n) h5, hDn]
      have h1L : 1 - 1 / L n ≠ 0 := by
        rw [sub_ne_zero]; intro h; rw [eq_div_iff hLn0] at h; linarith only [h, h5]
      field_simp
      ring
    have key : (ψ n - 1 / L n) * Dn =
        t * Real.sqrt (L n ^ 2 - L n ^ 2 * y n / (L n - 1) ^ 2) / Real.sqrt (M n) := by
      rw [← hxid, hx n]; ring
    have k2 : Real.sqrt (M n) * ((ψ n - 1 / L n) * Dn) =
        t * Real.sqrt (L n ^ 2 - L n ^ 2 * y n / (L n - 1) ^ 2) := by
      rw [key]; field_simp
    have k3 : 1 - L n * ψ n = -L n * (ψ n - 1 / L n) := by field_simp; ring
    show -L n * x n * t * Real.sqrt (L n ^ 2 - L n ^ 2 * y n / (L n - 1) ^ 2) / Dn =
      Real.sqrt (M n) * x n * (1 - L n * ψ n)
    rw [k3, div_eq_iff h6]
    linear_combination (L n * x n) * k2
  · have hden : Tendsto (fun n => (ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2) atTop
        (𝓝 ((1 / L0)⁻¹ ^ 2 - y0 / (1 - 1 / L0) ^ 2)) :=
      ((hψl.inv₀ (by positivity)).pow 2).sub (hy.div ((tendsto_const_nhds.sub hψl).pow 2)
        (by
          have : 1 - 1 / L0 ≠ 0 := by
            rw [sub_ne_zero]; intro h; rw [eq_div_iff hL0.ne'] at h; linarith only [h, hL1]
          exact pow_ne_zero 2 this))
    rw [sigma_psi L0 y0 hL1] at hden
    exact (hxl.pow 2).div hden hσ0sq.ne'

end

-- ===== from Assembly2.lean =====
section

/-- Re-join the spike rows and the null rows of a sample array. -/
def join {M N r p : ℕ} (e : Fin N ≃ Fin r ⊕ Fin p) (X1 : Fin M → Fin r → ℂ) (X2 : Fin M → Fin p → ℂ) :
    Fin M → Fin N → ℂ :=
  fun k j => Sum.elim (X1 k) (X2 k) (e j)

theorem join_inl {M N r p : ℕ} (e : Fin N ≃ Fin r ⊕ Fin p) (X1 : Fin M → Fin r → ℂ)
    (X2 : Fin M → Fin p → ℂ) (k : Fin M) (a : Fin r) : join e X1 X2 k (e.symm (Sum.inl a)) = X1 k a := by
  simp [join]

theorem join_inr {M N r p : ℕ} (e : Fin N ≃ Fin r ⊕ Fin p) (X1 : Fin M → Fin r → ℂ)
    (X2 : Fin M → Fin p → ℂ) (k : Fin M) (b : Fin p) : join e X1 X2 k (e.symm (Sum.inr b)) = X2 k b := by
  simp [join]

theorem join_split {M N r p : ℕ} (e : Fin N ≃ Fin r ⊕ Fin p) (X : Fin M → Fin N → ℂ) :
    join e (fun k a => X k (e.symm (Sum.inl a))) (fun k b => X k (e.symm (Sum.inr b))) = X := by
  funext k j
  unfold join
  cases h : e j with
  | inl a => simp only [Sum.elim_inl]; rw [← h, Equiv.symm_apply_apply]
  | inr b => simp only [Sum.elim_inr]; rw [← h, Equiv.symm_apply_apply]

theorem measurable_join {M N r p : ℕ} (e : Fin N ≃ Fin r ⊕ Fin p) :
    Measurable (fun z : (Fin M → Fin r → ℂ) × (Fin M → Fin p → ℂ) => join e z.1 z.2) := by
  refine measurable_pi_lambda _ fun k => measurable_pi_lambda _ fun j => ?_
  unfold join
  cases e j with
  | inl a => exact (measurable_pi_apply a).comp ((measurable_pi_apply k).comp measurable_fst)
  | inr b => exact (measurable_pi_apply b).comp ((measurable_pi_apply k).comp measurable_snd)

/-- Fubini over the row split: `P(E) = ∫ P_{X1}(join X1 X2 ∈ E) dP(X2)`. -/
theorem prob_split {M N r p : ℕ} (e : Fin N ≃ Fin r ⊕ Fin p) (E : Set (Fin M → Fin N → ℂ))
    (hE : MeasurableSet E) :
    (SpikedWishart.SoftEdge.sampleLaw M N).real E =
      ∫ X2, (SpikedWishart.SoftEdge.sampleLaw M r).real {X1 | join e X1 X2 ∈ E}
        ∂(SpikedWishart.SoftEdge.sampleLaw M p) := by
  have hf := sampleLaw_split (M := M) e
  set F := (fun z : (Fin M → Fin r → ℂ) × (Fin M → Fin p → ℂ) => join e z.1 z.2) ⁻¹' E with hFdef
  have hF : MeasurableSet F := hE.preimage (measurable_join e)
  have hEF : E = (fun X : Fin M → Fin N → ℂ => ((fun k a => X k (e.symm (Sum.inl a))),
      (fun k b => X k (e.symm (Sum.inr b))))) ⁻¹' F := by
    ext X; simp only [hFdef, Set.mem_preimage, join_split]
  have key : (SpikedWishart.SoftEdge.sampleLaw M N).real E =
      ((SpikedWishart.SoftEdge.sampleLaw M r).prod (SpikedWishart.SoftEdge.sampleLaw M p)).real F := by
    rw [hEF, measureReal_def, measureReal_def, hf.measure_preimage hF.nullMeasurableSet]
  rw [key, measureReal_def, Measure.prod_apply_symm hF,
    ← integral_toReal (measurable_measure_prodMk_right hF).aemeasurable
      (ae_of_all _ fun _ => measure_lt_top _ _)]
  rfl

theorem continuous_sampleCov_one (M : ℕ) {N : ℕ} (ℓ : Fin N → ℝ) :
    @Continuous (Fin M → Fin N → ℂ) (Fin N → Fin N → ℂ) _ _ (fun X => sampleCov M 1 ℓ X) := by
  have hd : Continuous (fun X : Fin M → Fin N → ℂ => dataMat M ℓ X) :=
    continuous_pi fun j => continuous_pi fun k =>
      continuous_const.mul ((continuous_apply j).comp (continuous_apply k))
  have h2 := (hd.matrix_mul hd.matrix_conjTranspose).const_smul ((M : ℂ)⁻¹)
  exact h2.congr (fun X => (sampleCov_one_eq M ℓ X).symm)

theorem measurableSet_eig_le (M : ℕ) {N : ℕ} [NeZero N] (ℓ : Fin N → ℝ) (x : ℝ) :
    MeasurableSet {X : Fin M → Fin N → ℂ | largestEig M 1 ℓ X ≤ x} := by
  have hset : {X : Fin M → Fin N → ℂ | largestEig M 1 ℓ X ≤ x} =
      {X | ((x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
        Matrix.of (sampleCov M 1 ℓ X : Fin N → Fin N → ℂ)).PosSemidef} := by
    ext X
    simp only [Set.mem_setOf_eq]
    rw [largestEig_le_iff, eig_le_iff_posSemidef]
    rfl
  rw [hset]
  exact measurableSet_psd (fun X => (sampleCov M 1 ℓ X : Fin N → Fin N → ℂ)) (continuous_sampleCov_one M ℓ).measurable
    (fun X => sampleCov_isHermitian M 1 ℓ X) x

/-- Null edge bound in PSD form. -/
theorem edge_psd {M p : ℕ} [NeZero p] (X2 : Fin M → Fin p → ℂ) (lam : ℝ)
    (h : largestEig M 1 (fun _ => 1) X2 ≤ lam) :
    ((lam : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ •
      ((Matrix.of X2)ᵀ * ((Matrix.of X2)ᵀ)ᴴ)).PosSemidef := by
  rw [largestEig_le_iff, eig_le_iff_posSemidef, sampleCov_one_eq] at h
  have hd : dataMat M (fun _ : Fin p => (1 : ℝ)) X2 = (Matrix.of X2)ᵀ := by
    ext j k; simp [dataMat]
  rw [hd] at h
  exact h

theorem psd_smul_one {n : Type*} [Fintype n] [DecidableEq n] (a : ℝ) (ha : 0 ≤ a) :
    ((a : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
  PosSemidef.one.smul (Complex.zero_le_real.mpr ha)

/-- The spiked-block limit DL with all hypotheses only eventually. -/
theorem detLimit_ev {k q : ℕ} (hk : 1 ≤ k) (hDL : DL_blockLimit)
    (C s₀ S₁ c x₀ : ℝ) (hs₀ : 0 < s₀) (hc : 0 < c) (hx₀ : 0 < x₀)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (hA : ∀ᶠ n in atTop, (A n).IsHermitian ∧
      (((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
        ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) ∧
      s₀ ≤ ((A n * A n).trace).re / M n ∧ ((A n * A n).trace).re / M n ≤ S₁)
    (L : ℕ → ℝ) (hL : ∀ n, c ≤ L n ∧ L n ≤ C)
    (D : ℕ → Fin (k + q) → ℝ) (hD1 : ∀ n i, D n (Fin.castAdd q i) = L n)
    (hD2 : ∀ n j, c ≤ D n (Fin.natAdd k j) ∧ D n (Fin.natAdd k j) ≤ L n - c)
    (x : ℕ → ℝ) (hx : ∀ᶠ n in atTop, x₀ ≤ x n) (t : ℝ)
    (ht : Tendsto (fun n => Real.sqrt (M n) * (x n - L n * (((A n).trace).re / M n)) /
        (L n * Real.sqrt (((A n * A n).trace).re / M n))) atTop (𝓝 t)) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
      {X | ((x n : ℂ) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ) -
        (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
          ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ)))).PosSemidef})
      atTop (𝓝 (G k t)) := by
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (hA.and hx)
  have h := hDL k q hk C s₀ S₁ c x₀ hs₀ hc hx₀ (fun n => M (n + n0))
    (hM.comp (tendsto_add_atTop_nat n0)) (fun n => A (n + n0))
    (fun n => (hn0 (n + n0) (by omega)).1.1) (fun n => (hn0 (n + n0) (by omega)).1.2.1)
    (fun n => (hn0 (n + n0) (by omega)).1.2.2.1) (fun n => (hn0 (n + n0) (by omega)).1.2.2.2)
    (fun n => L (n + n0)) (fun n => hL (n + n0)) (fun n => D (n + n0)) (fun n => hD1 (n + n0))
    (fun n => hD2 (n + n0)) (fun n => x (n + n0)) (fun n => (hn0 (n + n0) (by omega)).2) t
    ((tendsto_add_atTop_iff_nat n0).mpr ht)
  exact (tendsto_add_atTop_iff_nat n0).mp h

end

-- ===== from Assembly3.lean =====
section

set_option maxHeartbeats 4000000 in
/-- Core of Theorem 1.1(b) with convergent parameters `L_n → L0`, `N/M → y0` (Q1-Q4 as inputs). -/
theorem core {k q : ℕ} (hk : 1 ≤ k) (hQ1 : P2_nullEdge) (hQ2 : Q2_resolvent)
    (hDL : DL_blockLimit) (c C : ℝ) (hc : 0 < c) (M N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hMN : ∀ n, N n ≤ M n) (hr : ∀ n, k + q ≤ N n) (L : ℕ → ℝ)
    (hL : ∀ n, 1 + Real.sqrt ((N n : ℝ) / M n) + c ≤ L n ∧ L n ≤ C)
    (ℓ : ∀ n, Fin (N n) → ℝ)
    (hspike : ∀ n (j : Fin (N n)), (j : ℕ) < k → ℓ n j = L n)
    (hmid : ∀ n (j : Fin (N n)), k ≤ (j : ℕ) → (j : ℕ) < k + q → c ≤ ℓ n j ∧ ℓ n j ≤ L n - c)
    (hnull : ∀ n (j : Fin (N n)), k + q ≤ (j : ℕ) → ℓ n j = 1)
    (L0 y0 : ℝ) (hLl : Tendsto L atTop (𝓝 L0))
    (hyl : Tendsto (fun n => (N n : ℝ) / M n) atTop (𝓝 y0)) (t : ℝ) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
      {X | largestEig (M n) 1 (ℓ n) X ≤ L n + L n * ((N n : ℝ) / M n) / (L n - 1) +
        t * Real.sqrt (L n ^ 2 - L n ^ 2 * ((N n : ℝ) / M n) / (L n - 1) ^ 2) / Real.sqrt (M n)})
      atTop (𝓝 (G k t)) := by
  set y : ℕ → ℝ := fun n => (N n : ℝ) / M n with hydef
  set xs : ℕ → ℝ := fun n => L n + L n * y n / (L n - 1) +
    t * Real.sqrt (L n ^ 2 - L n ^ 2 * y n / (L n - 1) ^ 2) / Real.sqrt (M n) with hxsdef
  set p : ℕ → ℕ := fun n => N n - (k + q) with hpdef
  have hNpos : ∀ n, 0 < N n := fun n => by have := hr n; omega
  have hMpos : ∀ n, 0 < M n := fun n => lt_of_lt_of_le (hNpos n) (hMN n)
  have hMt : Tendsto M atTop atTop := tendsto_atTop_mono hMN hN
  have hy01 : ∀ n, 0 ≤ y n ∧ y n ≤ 1 := fun n => ⟨by positivity, by
    show (N n : ℝ) / M n ≤ 1
    rw [div_le_one (by exact_mod_cast hMpos n)]; exact_mod_cast hMN n⟩
  have hy0 : 0 ≤ y0 := ge_of_tendsto' hyl (fun n => (hy01 n).1)
  have hLge : 1 + Real.sqrt y0 + c ≤ L0 :=
    le_of_tendsto_of_tendsto' ((hyl.sqrt.const_add 1).add_const c) hLl (fun n => (hL n).1)
  have hgap : 1 + Real.sqrt y0 < L0 := by linarith only [hLge, hc]
  have hL1 : 1 < L0 := by linarith only [hgap, Real.sqrt_nonneg y0]
  have hL0 : 0 < L0 := by linarith only [hL1]
  set ψ : ℕ → ℝ := fun n =>
    ((xs n + 1 - y n) - Real.sqrt ((xs n + 1 - y n) ^ 2 - 4 * xs n)) / (2 * xs n) with hψdef
  obtain ⟨hψl, hsol, hxl, ha, hss⟩ := psi_asymp L y L0 y0 hLl hyl hy0 hgap M hMt t xs ψ
    (fun n => rfl) (fun n => rfl)
  have hL0m : 0 < L0 - 1 := by linarith only [hL1]
  have hy0lt : y0 < (L0 - 1) ^ 2 := by
    nlinarith only [Real.sq_sqrt hy0, Real.sqrt_nonneg y0, hgap]
  have hσ0sq : 0 < L0 ^ 2 - L0 ^ 2 * y0 / (L0 - 1) ^ 2 := by
    have h1 : y0 / (L0 - 1) ^ 2 < 1 := by rw [div_lt_one (pow_pos hL0m 2)]; exact hy0lt
    have h2 : L0 ^ 2 * y0 / (L0 - 1) ^ 2 = L0 ^ 2 * (y0 / (L0 - 1) ^ 2) := by ring
    rw [h2]; have h3 := mul_pos (pow_pos hL0 2) (sub_pos.mpr h1); linarith only [h3]
  set ρ0 := L0 + L0 * y0 / (L0 - 1) with hρ0
  set σsq := L0 ^ 2 - L0 ^ 2 * y0 / (L0 - 1) ^ 2 with hσsq
  have hσ0pos : 0 < Real.sqrt σsq := Real.sqrt_pos.mpr hσ0sq
  have hρ0pos : 0 < ρ0 := by
    have : 0 ≤ L0 * y0 / (L0 - 1) := div_nonneg (mul_nonneg hL0.le hy0) hL0m.le
    linarith only [this, hL0, hρ0]
  have hedge : 0 < ρ0 - (1 + Real.sqrt y0) ^ 2 := by
    rw [hρ0, rho_sub_edge L0 y0 hL1 hy0]
    have : 0 < L0 - 1 - Real.sqrt y0 := by linarith only [hgap]
    positivity
  set ε₁ := (ρ0 - (1 + Real.sqrt y0) ^ 2) / 3 with hε₁
  have hε₁pos : 0 < ε₁ := div_pos hedge (by norm_num)
  -- clamp for Q2
  set δ := c / (2 * L0) with hδ
  have hδpos : 0 < δ := div_pos hc (mul_pos two_pos hL0)
  have hδL : δ * L0 = c / 2 := by rw [hδ]; field_simp
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (mul_pos two_pos hL0)]; linarith only [hLge, Real.sqrt_nonneg y0, hc]
  set ψ₀ := (1 - δ) / (4 * L0) with hψ₀
  have hψ₀pos : 0 < ψ₀ := div_pos (by linarith only [hδ1]) (by linarith only [hL0])
  have hψ₀lt : ψ₀ < 1 / L0 := by
    rw [hψ₀, div_lt_div_iff₀ (by linarith only [hL0]) hL0]; linarith only [hδL, hL0, hc]
  set bd : ℕ → ℝ := fun n => (1 - δ) / (1 + Real.sqrt (y n)) with hbd
  have hψ₀bd : ∀ n, ψ₀ ≤ bd n := fun n => by
    have hs : Real.sqrt (y n) ≤ 1 := by
      have := Real.sqrt_le_sqrt (hy01 n).2; rwa [Real.sqrt_one] at this
    show (1 - δ) / (4 * L0) ≤ (1 - δ) / (1 + Real.sqrt (y n))
    exact div_le_div_of_nonneg_left (by linarith only [hδ1]) (by positivity) (by linarith only [hs, hL1])
  have hbdl : Tendsto bd atTop (𝓝 ((1 - δ) / (1 + Real.sqrt y0))) :=
    tendsto_const_nhds.div (hyl.sqrt.const_add 1) (by positivity)
  have hbd0 : 1 / L0 < (1 - δ) / (1 + Real.sqrt y0) := by
    rw [div_lt_div_iff₀ hL0 (by positivity)]; linarith only [hδL, hLge, hc]
  set ψ' : ℕ → ℝ := fun n => max ψ₀ (min (ψ n) (bd n)) with hψ'def
  have hψ'b : ∀ n, ψ₀ ≤ ψ' n ∧ ψ' n ≤ bd n := fun n =>
    ⟨le_max_left _ _, max_le (hψ₀bd n) (min_le_right _ _)⟩
  have hψ'ev : ∀ᶠ n in atTop, ψ' n = ψ n := by
    have e1 : ∀ᶠ n in atTop, ψ₀ < ψ n := hψl.eventually (eventually_gt_nhds hψ₀lt)
    have e2 : ∀ᶠ n in atTop, 0 < bd n - ψ n :=
      (hbdl.sub hψl).eventually (eventually_gt_nhds (sub_pos.mpr hbd0))
    filter_upwards [e1, e2] with n h1 h2
    show max ψ₀ (min (ψ n) (bd n)) = ψ n
    rw [min_eq_left (by linarith only [h2]), max_eq_right h1.le]
  -- Q2
  have hpM : ∀ n, p n ≤ M n := fun n => le_trans (Nat.sub_le _ _) (hMN n)
  have hpcast : ∀ n, ((p n : ℕ) : ℝ) = (N n : ℝ) - ((k + q : ℕ) : ℝ) := fun n => by
    show ((N n - (k + q) : ℕ) : ℝ) = _
    rw [Nat.cast_sub (hr n)]
  have hyp : ∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ ((k + q : ℕ) : ℝ) / M n := fun n => by
    refine ⟨(hy01 n).1, ?_⟩
    rw [hpcast n]
    show |(N n : ℝ) / M n - ((N n : ℝ) - ((k + q : ℕ) : ℝ)) / M n| ≤ ((k + q : ℕ) : ℝ) / M n
    rw [← sub_div, sub_sub_cancel, abs_of_nonneg (by positivity)]
  set x' : ℕ → ℝ := fun n => 1 / ψ' n + y n / (1 - ψ' n) with hx'def
  set A' : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n X =>
      1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x' n : ℂ) • 1 - (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)
    with hA'def
  set sst : ℕ → ℝ := fun n => x' n ^ 2 / ((ψ' n)⁻¹ ^ 2 - y n / (1 - ψ' n) ^ 2) with hsstdef
  have hQ2b : ∀ ε, 0 < ε →
      Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |Real.sqrt (M n) * ((((A' n X).trace).re / M n) - x' n * ψ' n)|}) atTop (𝓝 0) ∧
      Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |((A' n X * A' n X).trace).re / M n - sst n|}) atTop (𝓝 0) :=
    fun ε hε => hQ2 ((k + q : ℕ) : ℝ) ψ₀ δ hψ₀pos hδpos M p hMt hpM y ψ' hyp hψ'b ε hε
  obtain ⟨e, he0, he, heP⟩ := diag_seq (fun n ε =>
      (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |Real.sqrt (M n) * ((((A' n X).trace).re / M n) - x' n * ψ' n)|} +
      (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |((A' n X * A' n X).trace).re / M n - sst n|})
    (fun ε hε => by have := (hQ2b ε hε).1.add (hQ2b ε hε).2; rwa [add_zero] at this)
  -- Q1
  have hpt : Tendsto p atTop atTop := (tendsto_sub_atTop_nat (k + q)).comp hN
  have hQ1a := hQ1 ε₁ hε₁pos M p hpt hpM
  set lam' : ℕ → ℝ := fun n => (1 + Real.sqrt ((p n : ℝ) / M n)) ^ 2 + ε₁ with hlamdef
  -- bad and good sets
  set Bad : ∀ n, Set (Fin (M n) → Fin (p n) → ℂ) := fun n =>
    ({X | lam' n < largestEig (M n) 1 (fun _ => 1) X} ∪
    {X | e n < |Real.sqrt (M n) * ((((A' n X).trace).re / M n) - x' n * ψ' n)|}) ∪
    {X | e n < |((A' n X * A' n X).trace).re / M n - sst n|} with hBad
  set Good : ∀ n, Set (Fin (M n) → Fin (p n) → ℂ) := fun n =>
    (toMeasurable (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)) (Bad n))ᶜ with hGooddef
  have hGm : ∀ n, MeasurableSet (Good n) := fun n => (measurableSet_toMeasurable _ _).compl
  have hP2 : Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | e n < |Real.sqrt (M n) * ((((A' n X).trace).re / M n) - x' n * ψ' n)|} +
      (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | e n < |((A' n X * A' n X).trace).re / M n - sst n|}) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ?_, heP⟩
    exact lt_of_lt_of_le ha (add_nonneg measureReal_nonneg measureReal_nonneg)
  have hGood : Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real (Good n)ᶜ)
      atTop (𝓝 0) := by
    have hle : ∀ n, (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real (Good n)ᶜ ≤
        (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
          {X | lam' n < largestEig (M n) 1 (fun _ => 1) X} +
        ((SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
          {X | e n < |Real.sqrt (M n) * ((((A' n X).trace).re / M n) - x' n * ψ' n)|} +
        (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
          {X | e n < |((A' n X * A' n X).trace).re / M n - sst n|}) := fun n => by
      rw [hGooddef]
      simp only [compl_compl]
      rw [measureReal_def, measure_toMeasurable, ← measureReal_def]
      refine (measureReal_union_le _ _).trans ?_
      have := measureReal_union_le (μ := SpikedWishart.SoftEdge.sampleLaw (M n) (p n))
        {X | lam' n < largestEig (M n) 1 (fun _ => 1) X}
        {X | e n < |Real.sqrt (M n) * ((((A' n X).trace).re / M n) - x' n * ψ' n)|}
      linarith only [this]
    have hsum := hQ1a.add hP2
    rw [add_zero] at hsum
    exact squeeze_zero (fun n => measureReal_nonneg) hle hsum
  -- Fubini
  have hNeq : ∀ n, N n = (k + q) + p n := fun n => by
    have := hr n; show N n = (k + q) + (N n - (k + q)); omega
  let eN : ∀ n, Fin (N n) ≃ Fin (k + q) ⊕ Fin (p n) := fun n =>
    (finCongr (hNeq n)).trans finSumFinEquiv.symm
  have heN_inl : ∀ n (a : Fin (k + q)), (((eN n).symm (Sum.inl a) : Fin (N n)) : ℕ) = a := by
    intro n a; simp [eN]
  have heN_inr : ∀ n (b : Fin (p n)), (((eN n).symm (Sum.inr b) : Fin (N n)) : ℕ) = k + q + b := by
    intro n b; simp [eN]
  have hNZ : ∀ n, NeZero (N n) := fun n => ⟨(hNpos n).ne'⟩
  set h : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → ℝ := fun n X2 =>
    (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
      {X1 | join (eN n) X1 X2 ∈ {X | largestEig (M n) 1 (ℓ n) X ≤ xs n}} with hhdef
  have hEq : ∀ n, (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
      {X | largestEig (M n) 1 (ℓ n) X ≤ xs n} =
      ∫ X2, h n X2 ∂(SpikedWishart.SoftEdge.sampleLaw (M n) (p n)) := fun n => by
    haveI := hNZ n
    exact prob_split (eN n) _ (measurableSet_eig_le (M n) (ℓ n) (xs n))
  have hgoal : Tendsto (fun n => ∫ X2, h n X2 ∂(SpikedWishart.SoftEdge.sampleLaw (M n) (p n)))
      atTop (𝓝 (G k t)) := by
    refine integral_tendsto_of_pointwise _ h (fun n => ?_) (fun n X2 => ⟨measureReal_nonneg,
      measureReal_le_one⟩) Good hGm hGood _ ?_
    · haveI := hNZ n
      exact (measurable_measure_prodMk_right ((measurableSet_eig_le (M n) (ℓ n) (xs n)).preimage
        (measurable_join (eN n)))).ennreal_toReal
    intro ω hω
    have hnb : ∀ᶠ n in atTop, ω n ∉ Bad n :=
      hω.mono fun n hn hb => hn (subset_toMeasurable _ _ hb)
    have ev_p : ∀ᶠ n in atTop, 1 ≤ p n := hpt.eventually (eventually_ge_atTop 1)
    have hMr : Tendsto (fun n => (M n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hMt
    have hpyl : Tendsto (fun n => (p n : ℝ) / M n) atTop (𝓝 y0) := by
      have h1 : Tendsto (fun n => ((k + q : ℕ) : ℝ) / M n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hMr
      have h2 := hyl.sub h1
      rw [sub_zero] at h2
      refine h2.congr (fun n => ?_)
      rw [hpcast n, sub_div]
    have hlaml : Tendsto lam' atTop (𝓝 ((1 + Real.sqrt y0) ^ 2 + ε₁)) :=
      ((hpyl.sqrt.const_add 1).pow 2).add_const ε₁
    have ev_lt : ∀ᶠ n in atTop, lam' n + ε₁ < xs n := by
      have h3 : ∀ᶠ n in atTop, ε₁ < xs n - lam' n := (hxl.sub hlaml).eventually
        (eventually_gt_nhds (show ε₁ < ρ0 - ((1 + Real.sqrt y0) ^ 2 + ε₁) by rw [hε₁]; linarith only [hedge]))
      filter_upwards [h3] with n hn; linarith only [hn]
    have ev_xup : ∀ᶠ n in atTop, xs n < ρ0 + ε₁ := hxl.eventually (eventually_lt_nhds (by linarith only [hε₁pos]))
    have ev_xlo : ∀ᶠ n in atTop, ρ0 / 2 ≤ xs n := hxl.eventually (eventually_ge_nhds (by linarith only [hρ0pos]))
    have ev_x' : ∀ᶠ n in atTop, x' n = xs n := by
      filter_upwards [hψ'ev, hsol] with n h1 h2
      show 1 / ψ' n + y n / (1 - ψ' n) = xs n
      rw [h1]; exact h2
    have ev_ψ : ∀ᶠ n in atTop, x' n * ψ' n = xs n * ψ n := by
      filter_upwards [hψ'ev, ev_x'] with n h1 h2; rw [h1, h2]
    have ev_sst : ∀ᶠ n in atTop, sst n = xs n ^ 2 / ((ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2) := by
      filter_upwards [hψ'ev, ev_x'] with n h1 h2
      show x' n ^ 2 / ((ψ' n)⁻¹ ^ 2 - y n / (1 - ψ' n) ^ 2) = _
      rw [h1, h2]
    have hb : Tendsto (fun n => Real.sqrt (M n) * ((((A' n (ω n)).trace).re / M n) - x' n * ψ' n))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ he
      filter_upwards [hnb] with n hn
      rw [Real.norm_eq_abs]
      by_contra hc
      exact hn (Or.inl (Or.inr (not_le.mp hc)))
    have hsd : Tendsto (fun n => ((A' n (ω n) * A' n (ω n)).trace).re / M n - sst n) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ he
      filter_upwards [hnb] with n hn
      rw [Real.norm_eq_abs]
      by_contra hc
      exact hn (Or.inr (not_le.mp hc))
    set sLim := ρ0 ^ 2 / σsq with hsLim
    have hsLimpos : 0 < sLim := div_pos (pow_pos hρ0pos 2) hσ0sq
    have hsstl : Tendsto sst atTop (𝓝 sLim) := hss.congr' (ev_sst.mono fun n hn => hn.symm)
    have hsl : Tendsto (fun n => ((A' n (ω n) * A' n (ω n)).trace).re / M n) atTop (𝓝 sLim) := by
      have := hsd.add hsstl
      rw [zero_add] at this
      exact this.congr (fun n => by ring)
    have hnum : Tendsto (fun n => Real.sqrt (M n) * (xs n - L n * (((A' n (ω n)).trace).re / M n)))
        atTop (𝓝 (L0 * ρ0 * t / Real.sqrt σsq - L0 * 0)) := by
      refine (ha.sub (hLl.mul hb)).congr' ?_
      filter_upwards [ev_ψ] with n hn
      rw [hn]; ring
    have hden : Tendsto (fun n => L n * Real.sqrt (((A' n (ω n) * A' n (ω n)).trace).re / M n)) atTop
        (𝓝 (L0 * Real.sqrt sLim)) := hLl.mul hsl.sqrt
    have hsq : Real.sqrt sLim = ρ0 / Real.sqrt σsq := by
      rw [hsLim, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hρ0pos.le]
    have ht : Tendsto (fun n => Real.sqrt (M n) * (xs n - L n * (((A' n (ω n)).trace).re / M n)) /
        (L n * Real.sqrt (((A' n (ω n) * A' n (ω n)).trace).re / M n))) atTop (𝓝 t) := by
      have h4 := hnum.div hden (by rw [hsq]; exact (mul_pos hL0 (div_pos hρ0pos hσ0pos)).ne')
      have hval : (L0 * ρ0 * t / Real.sqrt σsq - L0 * 0) / (L0 * (ρ0 / Real.sqrt σsq)) = t := by
        rw [mul_zero, sub_zero]; field_simp
      rw [hsq, hval] at h4
      exact h4
    have hC0 : 0 < C := by
      linarith only [(hL 0).1, (hL 0).2, Real.sqrt_nonneg ((N 0 : ℝ) / M 0), hc]
    set C' := max C (ρ0 / ε₁ + 1) with hC'
    have hAev : ∀ᶠ n in atTop, (A' n (ω n)).IsHermitian ∧
        (((C' : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A' n (ω n)).PosSemidef ∧
          ((C' : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A' n (ω n)).PosSemidef) ∧
        sLim / 2 ≤ ((A' n (ω n) * A' n (ω n)).trace).re / M n ∧
        ((A' n (ω n) * A' n (ω n)).trace).re / M n ≤ sLim + 1 := by
      have es1 := hsl.eventually (eventually_ge_nhds (show sLim / 2 < sLim by linarith only [hsLimpos]))
      have es2 := hsl.eventually (eventually_le_nhds (lt_add_one sLim))
      filter_upwards [hnb, ev_p, ev_lt, ev_x', ev_xup, es1, es2] with n hn hp hlt hx' hxup h1 h2
      haveI : NeZero (p n) := ⟨by omega⟩
      have hB1 : largestEig (M n) 1 (fun _ => 1) (ω n) ≤ lam' n := by
        by_contra hc; exact hn (Or.inl (Or.inl (not_le.mp hc)))
      have hpsd := edge_psd (ω n) (lam' n) hB1
      have hlam0 : 0 ≤ lam' n := by
        exact add_nonneg (sq_nonneg _) hε₁pos.le
      have hlx : lam' n < x' n := by rw [hx']; linarith only [hlt, hε₁pos]
      have hAb := A_bounds (Matrix.of (ω n))ᵀ ((M n : ℝ)⁻¹) (x' n) (lam' n)
        (inv_pos.mpr (by exact_mod_cast hMpos n)) hlam0 hlx
        (by rw [Complex.ofReal_inv, Complex.ofReal_natCast]; exact hpsd)
      rw [Complex.ofReal_inv, Complex.ofReal_natCast] at hAb
      obtain ⟨hH, hup, -, hge1⟩ := hAb
      refine ⟨hH, ⟨?_, ?_⟩, h1, h2⟩
      · have hq : x' n / (x' n - lam' n) ≤ C' := by
          refine le_trans ?_ (le_max_right _ _)
          have hu : ρ0 / ε₁ * ε₁ = ρ0 := div_mul_cancel₀ _ hε₁pos.ne'
          have hu0 : 0 ≤ ρ0 / ε₁ := div_nonneg hρ0pos.le hε₁pos.le
          have hm := mul_le_mul_of_nonneg_left (show ε₁ ≤ x' n - lam' n by rw [hx']; linarith only [hlt])
            (show 0 ≤ ρ0 / ε₁ + 1 by linarith only [hu0])
          rw [div_le_iff₀ (by linarith only [hlx])]
          rw [hx'] at hm ⊢
          linarith only [hm, hu, hxup]
        have hsplit : (C' : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A' n (ω n) =
            ((((x' n / (x' n - lam' n)) : ℝ) : ℂ) • 1 - A' n (ω n)) +
              (((C' - x' n / (x' n - lam' n) : ℝ) : ℂ) • 1) := by
          rw [Complex.ofReal_sub, sub_smul]; abel
        rw [hsplit]
        exact hup.add (psd_smul_one _ (by linarith only [hq]))
      · have hsplit : (C' : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A' n (ω n) =
            (A' n (ω n) - 1) + (((C' + 1 : ℝ) : ℂ) • 1) := by
          rw [Complex.ofReal_add, add_smul, Complex.ofReal_one, one_smul]; abel
        rw [hsplit]
        exact hge1.add (psd_smul_one _ (by linarith only [le_max_left C (ρ0 / ε₁ + 1), hC0]))
    have hnull' : ∀ n (b : Fin (p n)), ℓ n ((eN n).symm (Sum.inr b)) = 1 := fun n b =>
      hnull n _ (by rw [heN_inr]; omega)
    set A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n => A' n (ω n) with hAdef
    set D : ℕ → Fin (k + q) → ℝ := fun n a => ℓ n ((eN n).symm (Sum.inl a)) with hDdef
    have hsec : ∀ᶠ n in atTop, (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
        {X | ((xs n : ℂ) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ) -
          (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
            ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ)))).PosSemidef} =
          h n (ω n) := by
      filter_upwards [hnb, ev_p, ev_lt, ev_x'] with n hn hp hlt hx'
      haveI := hNZ n
      haveI : NeZero (p n) := ⟨by omega⟩
      have hB1 : largestEig (M n) 1 (fun _ => 1) (ω n) ≤ lam' n := by
        by_contra hc; exact hn (Or.inl (Or.inl (not_le.mp hc)))
      have hpsd := edge_psd (ω n) (lam' n) hB1
      show _ = (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
        {X1 | join (eN n) X1 (ω n) ∈ {X | largestEig (M n) 1 (ℓ n) X ≤ xs n}}
      congr 1
      ext X1
      simp only [Set.mem_setOf_eq]
      rw [section_iff (eN n) (ℓ n) (hnull' n) (join (eN n) X1 (ω n)) (xs n) (lam' n) (by linarith only [hlt, hε₁pos])
        (by simp only [join_inr]; exact hpsd)]
      simp only [join_inl, join_inr, hAdef, hA'def, hDdef, hx']
    have hLc : ∀ n, c ≤ L n ∧ L n ≤ C' := fun n =>
      ⟨by linarith only [(hL n).1, Real.sqrt_nonneg ((N n : ℝ) / M n)], le_trans (hL n).2 (le_max_left _ _)⟩
    have hD1 : ∀ n i, D n (Fin.castAdd q i) = L n := fun n i =>
      hspike n _ (by rw [heN_inl]; simp)
    have hD2 : ∀ n j, c ≤ D n (Fin.natAdd k j) ∧ D n (Fin.natAdd k j) ≤ L n - c := fun n j =>
      hmid n _ (by rw [heN_inl]; simp) (by rw [heN_inl]; simp)
    refine Tendsto.congr' hsec ?_
    exact detLimit_ev hk hDL C' (sLim / 2) (sLim + 1) c (ρ0 / 2) (half_pos hsLimpos) hc
      (half_pos hρ0pos) M hMt A hAev L hLc D hD1 hD2 xs ev_xlo t ht
  exact hgoal.congr (fun n => (hEq n).symm)

end

-- ===== from GContinuous.lean =====
section

end

-- ===== from UnitaryReduce.lean =====
section

/-- `S(U) = U S(1) Uᴴ`: the sample covariance with rotation `U` is the conjugate of the
unrotated one. -/
theorem sampleCov_conj (M : ℕ) {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) :
    sampleCov M U ℓ G = U * sampleCov M 1 ℓ G * Uᴴ := by
  unfold sampleCov sampleVec
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.one_mulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- Two Hermitian matrices with the same characteristic polynomial have the same range of
eigenvalues. -/
theorem range_eigenvalues_eq {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    Set.range hA.eigenvalues = Set.range hB.eigenvalues := by
  have hr := hA.roots_charpoly_eq_eigenvalues
  rw [h, hB.roots_charpoly_eq_eigenvalues] at hr
  have key : ∀ (C D : Matrix (Fin N) (Fin N) ℂ) (hC : C.IsHermitian) (hD : D.IsHermitian),
      Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ hD.eigenvalues) Finset.univ.val =
        Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ hC.eigenvalues) Finset.univ.val →
      Set.range hC.eigenvalues ⊆ Set.range hD.eigenvalues := by
    intro C D hC hD hm x ⟨i, hi⟩
    have hmem : (((RCLike.ofReal : ℝ → ℂ) ∘ hC.eigenvalues) i : ℂ) ∈
        Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ hD.eigenvalues) Finset.univ.val := by
      rw [hm]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hmem
    refine ⟨j, ?_⟩
    have : ((hD.eigenvalues j : ℝ) : ℂ) = ((hC.eigenvalues i : ℝ) : ℂ) := hj
    rw [← hi]; exact_mod_cast this
  exact Set.Subset.antisymm (key A B hA hB hr) (key B A hB hA hr.symm)

/-- The largest eigenvalue does not depend on the unitary `U`: `λ₁(U) = λ₁(1)`. -/
theorem largestEig_unitary (M : ℕ) {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) (ℓ : Fin N → ℝ) (G : Fin M → Fin N → ℂ) :
    largestEig M U ℓ G = largestEig M 1 ℓ G := by
  unfold largestEig
  have hUU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).1 hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hcp : (sampleCov M U ℓ G).charpoly = (sampleCov M 1 ℓ G).charpoly := by
    rw [sampleCov_conj, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hUU,
      Matrix.mul_one]
  show sSup (Set.range _) = sSup (Set.range _)
  rw [range_eigenvalues_eq _ _ hcp]

end

-- ===== from Assembly4.lean =====
section

theorem ev_iff (a ρ s σ x : ℝ) (hs : 0 < s) (hσ : 0 < σ) :
    (a - ρ) * s / σ ≤ x ↔ a ≤ ρ + x * σ / s := by
  rw [div_le_iff₀ hσ, ← le_div_iff₀ hs, sub_le_iff_le_add']

/-- BBP Theorem 1.1(b) from the four analytic inputs Q1 (null edge), Q2 (resolvent statistics),
Q3 (sesquilinear CLT) and Q4 (GUE top-eigenvalue law). -/
theorem main_of_children (hQ1 : P2_nullEdge) (hQ2 : Q2_resolvent) (hDL : DL_blockLimit)
    (r k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) (γ₀ c C : ℝ) (hc : 0 < c)
    (M N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hγ : ∀ n, 1 ≤ Real.sqrt ((M n : ℝ) / N n) ∧ Real.sqrt ((M n : ℝ) / N n) ≤ γ₀)
    (hr : ∀ n, r ≤ N n)
    (U : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (hU : ∀ n, U n ∈ Matrix.unitaryGroup (Fin (N n)) ℂ)
    (L : ℕ → ℝ) (hL : ∀ n, 1 + (Real.sqrt ((M n : ℝ) / N n))⁻¹ + c ≤ L n ∧ L n ≤ C)
    (ℓ : ∀ n, Fin (N n) → ℝ)
    (hspike : ∀ n (j : Fin (N n)), (j : ℕ) < k → ℓ n j = L n)
    (hmid : ∀ n (j : Fin (N n)), k ≤ (j : ℕ) → (j : ℕ) < r → c ≤ ℓ n j ∧ ℓ n j ≤ L n - c)
    (hnull : ∀ n (j : Fin (N n)), r ≤ (j : ℕ) → ℓ n j = 1)
    (x : ℝ) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (largestEig (M n) (U n) (ℓ n) X -
              (L n + L n * (Real.sqrt ((M n : ℝ) / N n))⁻¹ ^ 2 / (L n - 1))) *
            Real.sqrt (M n) /
            Real.sqrt (L n ^ 2 - L n ^ 2 * (Real.sqrt ((M n : ℝ) / N n))⁻¹ ^ 2 / (L n - 1) ^ 2)
          ≤ x})
      atTop (𝓝 (G k x)) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = k + q := ⟨r - k, by omega⟩
  have hNpos : ∀ n, 0 < N n := fun n => by have := hr n; omega
  have hMN : ∀ n, N n ≤ M n := fun n => by
    have h1 := (hγ n).1
    rw [Real.one_le_sqrt] at h1
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hNpos n
    rw [one_le_div hNr] at h1
    exact_mod_cast h1
  have hMpos : ∀ n, 0 < M n := fun n => lt_of_lt_of_le (hNpos n) (hMN n)
  have hinv : ∀ n, (Real.sqrt ((M n : ℝ) / N n))⁻¹ = Real.sqrt ((N n : ℝ) / M n) := fun n => by
    rw [← Real.sqrt_inv, inv_div]
  have hL' : ∀ n, 1 + Real.sqrt ((N n : ℝ) / M n) + c ≤ L n ∧ L n ≤ C := fun n => by
    rw [← hinv n]; exact hL n
  have hset : ∀ n, {X | (largestEig (M n) (U n) (ℓ n) X -
              (L n + L n * (Real.sqrt ((M n : ℝ) / N n))⁻¹ ^ 2 / (L n - 1))) *
            Real.sqrt (M n) /
            Real.sqrt (L n ^ 2 - L n ^ 2 * (Real.sqrt ((M n : ℝ) / N n))⁻¹ ^ 2 / (L n - 1) ^ 2)
          ≤ x} = {X | largestEig (M n) 1 (ℓ n) X ≤ L n + L n * ((N n : ℝ) / M n) / (L n - 1) +
        x * Real.sqrt (L n ^ 2 - L n ^ 2 * ((N n : ℝ) / M n) / (L n - 1) ^ 2) / Real.sqrt (M n)} := by
    intro n
    have hg := gamma_inv_sq (M n) (N n) (hMpos n) (hNpos n)
    have hy0 : 0 ≤ (N n : ℝ) / M n := by positivity
    have hs0 := Real.sqrt_nonneg ((N n : ℝ) / M n)
    have hgap : Real.sqrt ((N n : ℝ) / M n) < L n - 1 := by linarith only [(hL' n).1, hc]
    have hlt : (N n : ℝ) / M n < (L n - 1) ^ 2 := by
      nlinarith only [Real.sq_sqrt hy0, hs0, hgap]
    have hL0 : 0 < L n := by linarith only [hgap, hs0]
    have hσ : 0 < L n ^ 2 - L n ^ 2 * ((N n : ℝ) / M n) / (L n - 1) ^ 2 := by
      have hpos : 0 < (L n - 1) ^ 2 := pow_pos (by linarith only [hgap, hs0]) 2
      have h1 : (N n : ℝ) / M n / (L n - 1) ^ 2 < 1 := by rw [div_lt_one hpos]; exact hlt
      have h2 : L n ^ 2 * ((N n : ℝ) / M n) / (L n - 1) ^ 2 =
          L n ^ 2 * ((N n : ℝ) / M n / (L n - 1) ^ 2) := by ring
      rw [h2]; have h3 := mul_pos (pow_pos hL0 2) (sub_pos.mpr h1); linarith only [h3]
    ext X
    simp only [Set.mem_setOf_eq]
    rw [largestEig_unitary _ _ (hU n), hg]
    exact ev_iff _ _ _ _ _ (Real.sqrt_pos.mpr (by exact_mod_cast hMpos n)) (Real.sqrt_pos.mpr hσ)
  have key : Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
      {X | largestEig (M n) 1 (ℓ n) X ≤ L n + L n * ((N n : ℝ) / M n) / (L n - 1) +
        x * Real.sqrt (L n ^ 2 - L n ^ 2 * ((N n : ℝ) / M n) / (L n - 1) ^ 2) / Real.sqrt (M n)})
      atTop (𝓝 (G k x)) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    have hbdd : Bornology.IsBounded (Set.Icc (0 : ℝ) C ×ˢ Set.Icc (0 : ℝ) 1) :=
      (Metric.isBounded_Icc 0 C).prod (Metric.isBounded_Icc 0 1)
    have hmem : ∀ n, (L (ns n), (N (ns n) : ℝ) / M (ns n)) ∈ Set.Icc (0 : ℝ) C ×ˢ Set.Icc (0 : ℝ) 1 :=
      fun n => by
        have h1 := hL' (ns n)
        have h2 := Real.sqrt_nonneg ((N (ns n) : ℝ) / M (ns n))
        refine ⟨⟨by linarith only [h1.1, h2, hc], h1.2⟩, ⟨by positivity, ?_⟩⟩
        rw [div_le_one (by exact_mod_cast hMpos (ns n))]
        exact_mod_cast hMN (ns n)
    obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd hmem
    have hσt : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
    refine ⟨φ, ?_⟩
    exact core hk hQ1 hQ2 hDL c C hc (fun n => M (ns (φ n)))
      (fun n => N (ns (φ n))) (hN.comp hσt) (fun n => hMN _) (fun n => hr _)
      (fun n => L (ns (φ n))) (fun n => hL' _) (fun n => ℓ (ns (φ n))) (fun n => hspike _)
      (fun n => hmid _) (fun n => hnull _) a.1 a.2 ((continuous_fst.tendsto a).comp hlim)
      ((continuous_snd.tendsto a).comp hlim) x
  refine key.congr (fun n => ?_)
  rw [hset n]

end

-- ===== from Assembly5.lean =====
section

/-- The edge bound without rate follows from the edge rate (`l = 0`). -/
theorem p2_nullEdge_of_rate (h : P2_edgeRate) : P2_nullEdge := by
  intro ε hε M N hN hNM
  have hM : Tendsto M atTop atTop := tendsto_atTop_mono hNM hN
  have h0 := h ε hε 0 M N hM hNM
  simpa only [pow_zero, one_mul] using h0

/-- `Q2_resolvent` from its two parts. -/
theorem q2_of_parts (hMo : Q2_moments) (hE : P2_edgeRate) (h1 : Q2_part1_of) (h2 : Q2_part2_of) :
    Q2_resolvent := by
  intro C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε hε
  have hP1 : Q2_part1 := h1 hMo hE
  exact ⟨hP1 C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε hε,
    h2 hP1 hE C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε hε⟩

end

end SpikedWishart.Separated.Lib

open SpikedWishart.Separated in
theorem solution (r k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) (γ₀ c C : ℝ) (hc : 0 < c)
    (M N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hγ : ∀ n, 1 ≤ Real.sqrt ((M n : ℝ) / N n) ∧ Real.sqrt ((M n : ℝ) / N n) ≤ γ₀)
    (hr : ∀ n, r ≤ N n)
    (U : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (hU : ∀ n, U n ∈ Matrix.unitaryGroup (Fin (N n)) ℂ)
    (L : ℕ → ℝ) (hL : ∀ n, 1 + (Real.sqrt ((M n : ℝ) / N n))⁻¹ + c ≤ L n ∧ L n ≤ C)
    (ℓ : ∀ n, Fin (N n) → ℝ)
    (hspike : ∀ n (j : Fin (N n)), (j : ℕ) < k → ℓ n j = L n)
    (hmid : ∀ n (j : Fin (N n)), k ≤ (j : ℕ) → (j : ℕ) < r → c ≤ ℓ n j ∧ ℓ n j ≤ L n - c)
    (hnull : ∀ n (j : Fin (N n)), r ≤ (j : ℕ) → ℓ n j = 1)
    (x : ℝ) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (largestEig (M n) (U n) (ℓ n) X -
              (L n + L n * (Real.sqrt ((M n : ℝ) / N n))⁻¹ ^ 2 / (L n - 1))) *
            Real.sqrt (M n) /
            Real.sqrt (L n ^ 2 - L n ^ 2 * (Real.sqrt ((M n : ℝ) / N n))⁻¹ ^ 2 / (L n - 1) ^ 2)
          ≤ x})
      atTop (𝓝 (G k x)) := by
  exact Lib.main_of_children (Lib.p2_nullEdge_of_rate SpikedWishart.Separated.null_wishart_top_eigenvalue_edge_rate) (Lib.q2_of_parts SpikedWishart.Separated.null_wishart_truncated_resolvent_trace_moments SpikedWishart.Separated.null_wishart_top_eigenvalue_edge_rate SpikedWishart.Separated.null_wishart_resolvent_trace_limit_of_moments SpikedWishart.Separated.null_wishart_resolvent_trace_square_limit_of_trace_limit) (SpikedWishart.Separated.spiked_block_psd_limit_of_sesquilinear_clt SpikedWishart.Separated.gaussian_sesquilinear_form_clt SpikedWishart.Separated.gue_top_eigenvalue_cdf)
    r k hk hkr γ₀ c C hc M N hN hγ hr U hU L hL ℓ hspike hmid hnull x
