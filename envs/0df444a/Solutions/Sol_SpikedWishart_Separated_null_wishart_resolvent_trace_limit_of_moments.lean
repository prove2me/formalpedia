-- Prove2me | solution 1 for SpikedWishart.Separated.null_wishart_resolvent_trace_limit_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:19:45.132066+00:00
-- url     : https://prove2.me/submissions/3af0db42-d0f4-40e6-a7d3-dc527cf6038a

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE

set_option autoImplicit false
set_option linter.all false

open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder
open Matrix
open scoped ComplexOrder Pointwise
open Filter Topology MeasureTheory Matrix Complex
open Filter Topology MeasureTheory Matrix Complex ProbabilityTheory
open scoped ENNReal
open Filter Topology MeasureTheory Matrix Polynomial ProbabilityTheory Complex
open Filter Topology MeasureTheory Matrix ProbabilityTheory Complex
open Filter Topology MeasureTheory

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

/-- Child: part (i) from the moment bounds and the edge rate (Chebyshev + root selection). -/
def Q2_part1_of : Prop := Q2_moments → P2_edgeRate → Q2_part1

end

-- ===== from LamMax.lean =====
section

variable {k : ℕ}

end

-- ===== from Misc.lean =====
section

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

end Blocks

end

-- ===== from Q1a.lean =====
section

/-! Q1 (sharp upper edge of the null complex Wishart matrix), deterministic part.
Bidiagonalisation bookkeeping: `Dec G α β` says `G = A + C` with `‖A‖ ≤ α`, `‖C‖ ≤ β` and the first
column of `C` zero; it is stable under the two Householder steps of Golub-Kahan bidiagonalisation. -/

/-- Squared Euclidean norm. -/
noncomputable def nsq {n : Type*} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

theorem nsq_nonneg {n : Type*} [Fintype n] (v : n → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

theorem nsq_eq_norm_sq {n : Type*} [Fintype n] (v : n → ℂ) :
    nsq v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [nsq, Complex.normSq_eq_norm_sq]

theorem nsq_eq_re {n : Type*} [Fintype n] (v : n → ℂ) : nsq v = (star v ⬝ᵥ v).re := by
  simp only [nsq, dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem nsq_unitary {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (v : n → ℂ) : nsq (U *ᵥ v) = nsq v := by
  rw [nsq_eq_re, nsq_eq_re, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    ← star_eq_conjTranspose, (mem_unitaryGroup_iff'.mp hU), one_mulVec]

/-- `‖A v‖ ≤ γ ‖v‖` for all `v`. -/
def Bnd {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (γ : ℝ) : Prop :=
  ∀ v : n → ℂ, nsq (A *ᵥ v) ≤ γ ^ 2 * nsq v

theorem Bnd.add {m n : Type*} [Fintype m] [Fintype n] {A C : Matrix m n ℂ} {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : Bnd A α) (hC : Bnd C β) : Bnd (A + C) (α + β) := by
  intro v
  have key : ∀ (B : Matrix m n ℂ) (γ : ℝ), 0 ≤ γ → Bnd B γ →
      Real.sqrt (nsq (B *ᵥ v)) ≤ γ * Real.sqrt (nsq v) := by
    intro B γ hγ hB
    rw [← Real.sqrt_sq hγ, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (hB v)
  have h1 := key A α hα hA
  have h2 := key C β hβ hC
  have h3 : Real.sqrt (nsq ((A + C) *ᵥ v)) ≤
      Real.sqrt (nsq (A *ᵥ v)) + Real.sqrt (nsq (C *ᵥ v)) := by
    simp only [nsq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _), add_mulVec, WithLp.toLp_add]
    exact norm_add_le _ _
  have h4 : Real.sqrt (nsq ((A + C) *ᵥ v)) ≤ (α + β) * Real.sqrt (nsq v) := by linarith
  have h5 := Real.sqrt_nonneg (nsq ((A + C) *ᵥ v))
  calc nsq ((A + C) *ᵥ v) = Real.sqrt (nsq ((A + C) *ᵥ v)) ^ 2 :=
        (Real.sq_sqrt (nsq_nonneg _)).symm
    _ ≤ ((α + β) * Real.sqrt (nsq v)) ^ 2 := pow_le_pow_left₀ h5 h4 2
    _ = (α + β) ^ 2 * nsq v := by rw [mul_pow, Real.sq_sqrt (nsq_nonneg _)]

theorem Bnd.unitary {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m n ℂ} {γ : ℝ} (hA : Bnd A γ) {U : Matrix m m ℂ} {W : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup m ℂ) (hW : W ∈ unitaryGroup n ℂ) : Bnd (U * A * W) γ := by
  intro v
  rw [← mulVec_mulVec, ← mulVec_mulVec, nsq_unitary hU]
  calc nsq (A *ᵥ (W *ᵥ v)) ≤ γ ^ 2 * nsq (W *ᵥ v) := hA _
    _ = γ ^ 2 * nsq v := by rw [nsq_unitary hW]

/-- Decomposition `G = A + C`, `‖A‖ ≤ α`, `‖C‖ ≤ β`, first column of `C` zero. -/
def Dec {M N : ℕ} (G : Matrix (Fin M) (Fin N) ℂ) (α β : ℝ) : Prop :=
  ∃ A C : Matrix (Fin M) (Fin N) ℂ, G = A + C ∧ Bnd A α ∧ Bnd C β ∧
    ∀ (i : Fin M) (j : Fin N), (j : ℕ) = 0 → C i j = 0

theorem Dec.unitary {M N : ℕ} {G : Matrix (Fin M) (Fin N) ℂ} {α β : ℝ} (h : Dec G α β)
    {U : Matrix (Fin M) (Fin M) ℂ} {W : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ unitaryGroup (Fin M) ℂ) (hW : W ∈ unitaryGroup (Fin N) ℂ)
    (hW0 : ∀ k j : Fin N, (j : ℕ) = 0 → (k : ℕ) ≠ 0 → W k j = 0) : Dec (U * G * W) α β := by
  obtain ⟨A, C, rfl, hA, hC, h0⟩ := h
  refine ⟨U * A * W, U * C * W, by rw [Matrix.mul_add, Matrix.add_mul], hA.unitary hU hW, hC.unitary hU hW, ?_⟩
  intro i j hj
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) = 0
  · have : (U * C) i k = 0 := by
      rw [mul_apply]; exact Finset.sum_eq_zero fun l _ => by rw [h0 l k hk, mul_zero]
    rw [this, zero_mul]
  · rw [hW0 k j hj hk, mul_zero]

end

-- ===== from Q1b.lean =====
section

/-! Q1, Householder reflection: a measurable unitary `rot v` with `rot v *ᵥ v = z • e₀`, `‖z‖ = ‖v‖`. -/

/-- First basis vector. -/
def e0v (m : ℕ) : Fin (m + 1) → ℂ := fun i => if (i : ℕ) = 0 then 1 else 0

/-- Phase of a complex number (`1` at `0`). -/
noncomputable def phs (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

/-- Householder matrix `1 - (2/‖w‖²) w wᴴ`. -/
noncomputable def hh {n : Type*} [Fintype n] [DecidableEq n] (w : n → ℂ) : Matrix n n ℂ :=
  1 - (((2 / nsq w : ℝ)) : ℂ) • vecMulVec w (star w)

/-- Householder target coefficient `z = -‖v‖ · phase(v₀)`. -/
noncomputable def rz {m : ℕ} (v : Fin (m + 1) → ℂ) : ℂ := -((Real.sqrt (nsq v) : ℝ) : ℂ) * phs (v 0)

noncomputable def rot {m : ℕ} (v : Fin (m + 1) → ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  if v = 0 then 1 else hh (v - rz v • e0v m)

end

-- ===== from Q3a.lean =====
section

end

-- ===== from Q3b.lean =====
section

end

-- ===== from Q1c.lean =====
section

/-! Q1, laws of one Golub-Kahan step: the column norm, the rotated row and the rotated
`(M-1) × (N-1)` remainder of an i.i.d. complex Gaussian array. Needs Q1a, Q1b, Q3a, Q3b. -/

end

-- ===== from Q1d.lean =====
section

/-! Q1 = `P2_nullEdge`: induction over the Golub-Kahan steps, Chernoff bounds for `Γ(m,1)` tails, and
the final edge estimate. Needs ChildStatements, LamMax, Misc, SchurEig, BlockForm, Q1a, Q1b, Q3a, Q3b, Q1c. -/

end

-- ===== from Q3c.lean =====
section

theorem herm_decomp {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

end

-- ===== from W5a.lean =====
section

namespace Weyl

theorem isProb_cg : IsProbabilityMeasure SpikedWishart.SoftEdge.stdComplexGaussian := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian
  exact Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

end Weyl

end

-- ===== from Q2a.lean =====
section

namespace Q2

/-- `G (x - S) = 1` gives `G S = x G - 1`. -/
theorem G_mul_S {p : ℕ} (S : Matrix (Fin p) (Fin p) ℂ) (x : ℂ)
    (hdet : IsUnit (x • (1 : Matrix (Fin p) (Fin p) ℂ) - S).det) :
    (x • (1 : Matrix (Fin p) (Fin p) ℂ) - S)⁻¹ * S =
      x • (x • (1 : Matrix (Fin p) (Fin p) ℂ) - S)⁻¹ - 1 := by
  set G := (x • (1 : Matrix (Fin p) (Fin p) ℂ) - S)⁻¹ with hG
  have h : G * (x • (1 : Matrix (Fin p) (Fin p) ℂ) - S) = 1 := Matrix.nonsing_inv_mul _ hdet
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at h
  calc G * S = x • G - (x • G - G * S) := by abel
    _ = x • G - 1 := by rw [h]

/-- Trace of the resolvent-quadratic matrix `A = 1 + M⁻¹ Yᴴ (x - M⁻¹YYᴴ)⁻¹ Y`. -/
theorem trace_A {M p : ℕ} (Y : Matrix (Fin p) (Fin M) ℂ) (x : ℂ)
    (hdet : IsUnit (x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ)).det) :
    (1 + (M : ℂ)⁻¹ • (Yᴴ * (x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ))⁻¹ * Y)).trace =
      M - p + x * ((x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ))⁻¹).trace := by
  set G := (x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ))⁻¹ with hG
  have hc : ((M : ℂ)⁻¹ • (Yᴴ * G * Y)).trace = (G * ((M : ℂ)⁻¹ • (Y * Yᴴ))).trace := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Yᴴ]
    simp only [Matrix.mul_assoc]
  rw [trace_add, hc, hG, G_mul_S _ x hdet, trace_sub, trace_smul, trace_one, trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  ring

end Q2

end

-- ===== from Q2b.lean =====
section

namespace Q2

/-- The i.i.d. complex Gaussian vector law. -/
noncomputable abbrev cgv (n : ℕ) : Measure (Fin n → ℂ) :=
  Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian

end Q2

end

-- ===== from Q2c.lean =====
section

namespace Q2

theorem iob {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {φ : α → ℝ}
    (hφ : Measurable φ) (C : ℝ) (h : ∀ x, |φ x| ≤ C) : Integrable φ μ :=
  Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact h x))

theorem abs_int_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {φ : α → ℝ}
    (C : ℝ) (h : ∀ x, |φ x| ≤ C) : |∫ x, φ x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := φ) (C := C)
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact h x))
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

end Q2

end

-- ===== from Q2d.lean =====
section

namespace Q2

/-- Inverse of `x - K` in the eigenbasis of `K`. -/
theorem inv_eig {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) (x : ℝ)
    (hx : ∀ i, hK.eigenvalues i ≠ x) :
    ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ =
      (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) *
        diagonal (fun i => (((x - hK.eigenvalues i)⁻¹ : ℝ) : ℂ)) *
        star (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) := by
  set U := (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) with hUdef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hK.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hK.eigenvectorUnitary
  have hd : K = U * diagonal (fun i => ((hK.eigenvalues i : ℝ) : ℂ)) * star U := herm_decomp hK
  have h1 : (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) = U * diagonal (fun _ => (x : ℂ)) * star U := by
    rw [show diagonal (fun _ => (x : ℂ)) = (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) by
      ext i j; simp [diagonal_apply, one_apply], Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU']
  have h2 : (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K =
      (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - U * diagonal (fun i => ((hK.eigenvalues i : ℝ) : ℂ)) * star U := by
    rw [← hd]
  have h3 : (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K =
      U * diagonal (fun i => (((x - hK.eigenvalues i : ℝ)) : ℂ)) * star U := by
    rw [h2, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    congr 3
    funext i
    push_cast
    ring
  apply Matrix.inv_eq_right_inv
  rw [h3]
  calc U * diagonal (fun i => (((x - hK.eigenvalues i : ℝ)) : ℂ)) * star U *
        (U * diagonal (fun i => (((x - hK.eigenvalues i)⁻¹ : ℝ) : ℂ)) * star U)
      = U * (diagonal (fun i => (((x - hK.eigenvalues i : ℝ)) : ℂ)) * (star U * U) *
        diagonal (fun i => (((x - hK.eigenvalues i)⁻¹ : ℝ) : ℂ))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * star U := by
        rw [hUU, Matrix.mul_one, diagonal_mul_diagonal]
        have : (fun i => (((x - hK.eigenvalues i : ℝ)) : ℂ) * (((x - hK.eigenvalues i)⁻¹ : ℝ) : ℂ)) =
            fun _ => (1 : ℂ) := by
          funext i
          have hne : (x - hK.eigenvalues i : ℝ) ≠ 0 := sub_ne_zero.mpr (hx i).symm
          rw [← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one]
        rw [this, diagonal_one, Matrix.mul_one]
    _ = 1 := hUU'

/-- Trace of a matrix in conjugated diagonal form. -/
theorem trace_conj_diag {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : star U * U = 1) (d : Fin p → ℂ) :
    trace (U * diagonal d * star U) = ∑ i, d i := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, trace_diagonal]

end Q2

end

-- ===== from Q2e.lean =====
section

namespace Q2

/-- The sample covariance `M⁻¹ Y Yᴴ`, `Y = (of X)ᵀ`, with columns `X k`. -/
noncomputable def Smat {M p : ℕ} (X : Fin M → Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ)

open scoped ComplexOrder

/-- `Re tr (x - K)⁻¹`. -/
noncomputable def resT {p : ℕ} (x : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) : ℝ :=
  (trace (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹)).re

/-- `Re tr (x - K)⁻²`. -/
noncomputable def resT2 {p : ℕ} (x : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) : ℝ :=
  (trace (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ *
    ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹)).re

theorem unit_of_eig {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) {x : ℝ}
    (h : ∀ i, hK.eigenvalues i < x) : IsUnit ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K).det := by
  have hpd := (eig_lt_iff_posDef hK x).mp h
  exact isUnit_iff_ne_zero.mpr hpd.det_pos.ne'

theorem res_diag {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) (x : ℝ)
    (hx : ∀ i, hK.eigenvalues i ≠ x) (k : ℕ) :
    (trace ((((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) ^ k)).re =
      ∑ i, ((x - hK.eigenvalues i)⁻¹) ^ k := by
  rw [inv_eig hK x hx]
  set U := (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) with hUdef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hK.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hK.eigenvectorUnitary
  set d : Fin p → ℂ := fun i => (((x - hK.eigenvalues i)⁻¹ : ℝ) : ℂ) with hd
  have hpow : ∀ j : ℕ, (U * diagonal d * star U) ^ j = U * diagonal (d ^ j) * star U := by
    intro j
    induction j with
    | zero => simp [hUU']
    | succ j ih =>
      rw [pow_succ, ih, pow_succ,
        show diagonal (d ^ j * d) = diagonal (d ^ j) * diagonal d from (diagonal_mul_diagonal _ _).symm]
      calc U * diagonal (d ^ j) * star U * (U * diagonal d * star U)
          = U * diagonal (d ^ j) * (star U * U) * diagonal d * star U := by simp only [Matrix.mul_assoc]
        _ = U * (diagonal (d ^ j) * diagonal d) * star U := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [hpow, trace_conj_diag U hUU, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.pow_apply, hd]
  simp only []
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem sum_inv_pow_le {p : ℕ} (μ : Fin p → ℝ) {x e1 : ℝ} (hx : e1 < x) (hμ : ∀ i, μ i ≤ e1) (k : ℕ) :
    0 ≤ ∑ i, ((x - μ i)⁻¹) ^ k ∧ ∑ i, ((x - μ i)⁻¹) ^ k ≤ p * ((x - e1)⁻¹) ^ k := by
  have h1 : ∀ i, 0 ≤ (x - μ i)⁻¹ := fun i => inv_nonneg.mpr (by linarith [hμ i])
  have h2 : ∀ i, (x - μ i)⁻¹ ≤ (x - e1)⁻¹ := fun i => inv_anti₀ (by linarith) (by linarith [hμ i])
  constructor
  · exact Finset.sum_nonneg (fun i _ => pow_nonneg (h1 i) k)
  · calc ∑ i, ((x - μ i)⁻¹) ^ k ≤ ∑ _i : Fin p, ((x - e1)⁻¹) ^ k :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (h1 i) (h2 i) k)
      _ = p * ((x - e1)⁻¹) ^ k := by simp

/-- The per-coordinate constant. -/
noncomputable def condC (p M : ℕ) (x e1 : ℝ) : ℝ :=
  2 / ((x - e1) / (2 * x)) ^ 2 * ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 4) +
    8 * ((M : ℝ)⁻¹ * (p * ((x - e1)⁻¹) ^ 2)) ^ 2 / ((x - e1) / (2 * x)) ^ 4 * ((M : ℝ)⁻¹) ^ 2 *
      (p * ((x - e1)⁻¹) ^ 2)

theorem condC_nonneg (p M : ℕ) (x e1 : ℝ) : 0 ≤ condC p M x e1 := by
  unfold condC; positivity

theorem isClosed_good {k : ℕ} (x : ℝ) :
    IsClosed {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef} := by
  have : OrderClosedTopology ℂ := Complex.orderClosedTopology
  have hset : {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef} =
      {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A)ᴴ =
        (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A} ∩
      ⋂ v : Fin k → ℂ, {A : Matrix (Fin k) (Fin k) ℂ |
        0 ≤ star v ⬝ᵥ (((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A) *ᵥ v)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [hset]
  have hc : Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A) :=
    continuous_const.sub continuous_id
  refine (isClosed_eq hc.matrix_conjTranspose hc).inter (isClosed_iInter fun v => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (hc.matrix_mulVec continuous_const)

theorem continuous_Smat {M p : ℕ} : Continuous (fun X : Fin M → Fin p → ℂ => Smat X) := by
  unfold Smat
  have h : Continuous (fun X : Fin M → Fin p → ℂ => (Matrix.of X)ᵀ) := continuous_id.matrix_transpose
  exact (h.matrix_mul h.matrix_conjTranspose).const_smul ((M : ℂ)⁻¹)

theorem Smat_psd {M p : ℕ} (X : Fin M → Fin p → ℂ) : (Smat X).PosSemidef := by
  have e : (M : ℂ)⁻¹ = (((M : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  unfold Smat
  rw [e]
  exact (posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.mpr (by positivity))

theorem meas_inv_entry {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] {p : ℕ}
    {f : α → Matrix (Fin p) (Fin p) ℂ} (hf : Continuous f) (x : ℝ) (i j : Fin p) :
    Measurable (fun a => (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - f a)⁻¹) i j) := by
  have hc : Continuous (fun a => (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - f a) := continuous_const.sub hf
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul ((hc.matrix_adjugate.matrix_elem i j).measurable)

theorem measurable_resT {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] {p : ℕ}
    {f : α → Matrix (Fin p) (Fin p) ℂ} (hf : Continuous f) (x : ℝ) :
    Measurable (fun a => resT x (f a)) := by
  unfold resT
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.measurable_sum _ (fun i _ => Complex.measurable_re.comp (meas_inv_entry hf x i i))

theorem res_bounds {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) {x e1 : ℝ} (hx : e1 < x)
    (hKe : ∀ i, hK.eigenvalues i ≤ e1) :
    0 ≤ resT x K ∧ resT x K ≤ p * (x - e1)⁻¹ ∧ 0 ≤ resT2 x K ∧ resT2 x K ≤ p * ((x - e1)⁻¹) ^ 2 := by
  have hne : ∀ i, hK.eigenvalues i ≠ x := fun i => ne_of_lt (by linarith [hKe i])
  have h1 := res_diag hK x hne 1
  have h2 := res_diag hK x hne 2
  rw [pow_one] at h1
  rw [sq] at h2
  have b1 := sum_inv_pow_le (hK.eigenvalues) hx hKe 1
  have b2 := sum_inv_pow_le (hK.eigenvalues) hx hKe 2
  simp only [pow_one] at b1
  have r1 : resT x K = ∑ i, ((x - hK.eigenvalues i)⁻¹) := by unfold resT; rw [h1]; simp
  have r2 : resT2 x K = ∑ i, ((x - hK.eigenvalues i)⁻¹) ^ 2 := by unfold resT2; rw [h2]
  rw [r1, r2]
  exact ⟨b1.1, b1.2, b2.1, b2.2⟩

open Classical in
/-- Truncated trace `F = 1_{S <= e1} Re tr (x - S)⁻¹`. -/
noncomputable def Ff {M p : ℕ} (x e1 : ℝ) (X : Fin M → Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then resT x (Smat X) else 0

/-- The bound for `Φ_k`. -/
noncomputable def bnd0 (p M : ℕ) (x e1 : ℝ) : ℝ :=
  p * (x - e1)⁻¹ + 2 * ((M : ℝ)⁻¹ * (p * ((x - e1)⁻¹) ^ 2)) / ((x - e1) / (2 * x))

theorem measurable_Ff {M p : ℕ} (x e1 : ℝ) : Measurable (fun X : Fin M → Fin p → ℂ => Ff x e1 X) := by
  unfold Ff
  exact Measurable.ite (((isClosed_good e1).preimage continuous_Smat).measurableSet)
    (measurable_resT continuous_Smat x) measurable_const

theorem Ff_bound {M p : ℕ} {x e1 : ℝ} (hx : e1 < x) (X : Fin M → Fin p → ℂ) :
    |Ff x e1 X| ≤ p * (x - e1)⁻¹ := by
  have ha : 0 ≤ (p : ℝ) * (x - e1)⁻¹ := mul_nonneg (Nat.cast_nonneg p) (inv_nonneg.mpr (by linarith))
  unfold Ff
  split_ifs with hg
  · have hH := (Smat_psd X).isHermitian
    have hb := res_bounds hH hx ((eig_le_iff_posSemidef hH e1).mpr hg)
    rw [abs_of_nonneg hb.1]; exact hb.2.1
  · simpa using ha

open Classical in
/-- Variance of the truncated trace (Efron-Stein with leave-one-out proxies). -/
theorem var_Ff [Fact Q2_moments] {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) :
    ∫ X, (Ff x e1 X - ∫ Y, Ff x e1 Y ∂SpikedWishart.SoftEdge.sampleLaw M p) ^ 2
        ∂SpikedWishart.SoftEdge.sampleLaw M p ≤
      M * (condC p M x e1 + bnd0 p M x e1 ^ 2 * (SpikedWishart.SoftEdge.sampleLaw M p).real
        {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef}) := by
  exact ((Fact.out : Q2_moments) M p hM x e1 he1 hx).1

end Q2

end

-- ===== from Q2f.lean =====
section

namespace Q2

end Q2

end

-- ===== from Q2g.lean =====
section

namespace Q2

end Q2

end

-- ===== from Q2h.lean =====
section

namespace Q2

/-! BIAS: the mean `c = E F / M` of the truncated normalized trace nearly solves `x c - p/M = c/(1-c)`. -/

/-- Probability of the bad event `λmax S > e1`. -/
noncomputable def Pbad (M p : ℕ) (e1 : ℝ) : ℝ :=
  (SpikedWishart.SoftEdge.sampleLaw M p).real
    {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef}

/-- The mean normalized truncated trace. -/
noncomputable def cbar (M p : ℕ) (x e1 : ℝ) : ℝ :=
  (∫ X, Ff x e1 X ∂SpikedWishart.SoftEdge.sampleLaw M p) / M

/-- The explicit bias error. -/
noncomputable def biasErr (p M : ℕ) (x e1 Pb : ℝ) : ℝ :=
  4 / ((x - e1) / (2 * x)) ^ 2 * ((((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) + Pb) / 2 + Pb +
      (M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x)))) +
    4 / ((x - e1) / (2 * x)) ^ 3 * (4 * (((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) +
      (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pb) / M + Pb +
      ((M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x)))) ^ 2)) +
    ((p : ℝ) / M + 2 / ((x - e1) / (2 * x))) * Pb

theorem isProb_law (M p : ℕ) : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw M p) := by
  have := Weyl.isProb_cg
  have hν : IsProbabilityMeasure (cgv p) := by unfold cgv; infer_instance
  show IsProbabilityMeasure (Measure.pi fun _ : Fin M => cgv p)
  infer_instance

theorem iob2 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {φ : α → ℝ}
    (hφ : Measurable φ) (C : ℝ) (h : ∀ x, |φ x| ≤ C) : Integrable (fun x => φ x ^ 2) μ :=
  iob (hφ.pow_const 2) (C ^ 2) (fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h x) 2)

theorem bias [Fact Q2_moments] {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x)
    (hsmall : (((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) + Pbad M p e1) / 2 +
      (M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x))) ≤ (x - e1) / (2 * x) / 2) :
    0 ≤ cbar M p x e1 ∧ cbar M p x e1 ≤ 1 - (x - e1) / (2 * x) / 2 ∧
      |x * cbar M p x e1 - p / M - cbar M p x e1 / (1 - cbar M p x e1)| ≤ biasErr p M x e1 (Pbad M p e1) := by
  exact ((Fact.out : Q2_moments) M p hM x e1 he1 hx).2 hsmall

end Q2

end

-- ===== from Q2i.lean =====
section

namespace Q2

/-! ROOT SELECTION: `c(x) = cbar` is continuous in `x`, nearly solves the quadratic for every `x ≥ x1`, and is
small for large `x`; so (IVT) it stays below the midpoint of the two roots, hence near the small root. -/

theorem resT_eq_sum {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) {x e1 : ℝ} (hx : e1 < x)
    (hKe : ∀ i, hK.eigenvalues i ≤ e1) : resT x K = ∑ i, (x - hK.eigenvalues i)⁻¹ := by
  have hne : ∀ i, hK.eigenvalues i ≠ x := fun i => ne_of_lt (by linarith [hKe i])
  have h := res_diag hK x hne 1
  simp only [pow_one] at h
  exact h

theorem continuousOn_resT {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) {e1 : ℝ}
    (hKe : ∀ i, hK.eigenvalues i ≤ e1) : ContinuousOn (fun x => resT x K) (Set.Ioi e1) := by
  have heq : Set.EqOn (fun x => resT x K) (fun x => ∑ i, (x - hK.eigenvalues i)⁻¹) (Set.Ioi e1) :=
    fun x hx => resT_eq_sum hK hx hKe
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine (continuousOn_id.sub continuousOn_const).inv₀ (fun x hx => ?_)
  have : e1 < x := hx
  have h2 := hKe i
  exact sub_ne_zero.mpr (ne_of_gt (show hK.eigenvalues i < x by linarith))

theorem continuousOn_cbar (M p : ℕ) {e1 x1 : ℝ} (hx1 : e1 < x1) :
    ContinuousOn (fun x => cbar M p x e1) (Set.Ici x1) := by
  have := isProb_law M p
  unfold cbar
  refine ContinuousOn.div_const ?_ _
  refine continuousOn_of_dominated (bound := fun _ => (p : ℝ) * (x1 - e1)⁻¹)
    (fun x _ => (measurable_Ff x e1).aestronglyMeasurable) (fun x hx => ae_of_all _ (fun X => ?_))
    (integrable_const _) (ae_of_all _ (fun X => ?_))
  · have hx' : x1 ≤ x := hx
    rw [Real.norm_eq_abs]
    refine (Ff_bound (by linarith) X).trans ?_
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith) (by linarith)) (Nat.cast_nonneg p)
  · unfold Ff
    split_ifs with hg
    · have hH := (Smat_psd X).isHermitian
      exact (continuousOn_resT hH ((eig_le_iff_posSemidef hH e1).mpr hg)).mono
        (fun x hx => lt_of_lt_of_le hx1 hx)
    · exact continuousOn_const

theorem cbar_le {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (hx : e1 < x) :
    cbar M p x e1 ≤ (p : ℝ) / M * (x - e1)⁻¹ := by
  have := isProb_law M p
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  unfold cbar
  have h := abs_int_le (μ := SpikedWishart.SoftEdge.sampleLaw M p) _ (Ff_bound (M := M) (p := p) hx (e1 := e1))
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hMp]
  exact (le_abs_self _).trans h

/-- Abstract forms of the error constants, in `κ` and `a = (x - e1)⁻¹`. -/
noncomputable def condF (p M : ℕ) (κ a : ℝ) : ℝ :=
  2 / κ ^ 2 * ((M : ℝ)⁻¹) ^ 2 * (p * a ^ 4) + 8 * ((M : ℝ)⁻¹ * (p * a ^ 2)) ^ 2 / κ ^ 4 * ((M : ℝ)⁻¹) ^ 2 *
    (p * a ^ 2)

noncomputable def bndF (p M : ℕ) (κ a : ℝ) : ℝ :=
  p * a + 2 * ((M : ℝ)⁻¹ * (p * a ^ 2)) / κ

noncomputable def errF (p M : ℕ) (κ a Pb : ℝ) : ℝ :=
  4 / κ ^ 2 * ((((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + Pb) / 2 + Pb + (M : ℝ)⁻¹ * (a / κ)) +
    4 / κ ^ 3 * (4 * (((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + (condF p M κ a + bndF p M κ a ^ 2 * Pb) / M + Pb +
      ((M : ℝ)⁻¹ * (a / κ)) ^ 2)) +
    ((p : ℝ) / M + 2 / κ) * Pb

noncomputable def smallF (p M : ℕ) (κ a Pb : ℝ) : ℝ :=
  (((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + Pb) / 2 + (M : ℝ)⁻¹ * (a / κ)

theorem biasErr_eq (p M : ℕ) (x e1 Pb : ℝ) :
    biasErr p M x e1 Pb = errF p M ((x - e1) / (2 * x)) (x - e1)⁻¹ Pb := rfl

theorem condF_anti (p M : ℕ) {κ κ1 a a1 : ℝ} (hκ1 : 0 < κ1) (hκ : κ1 ≤ κ) (ha : 0 ≤ a) (ha1 : a ≤ a1) :
    condF p M κ a ≤ condF p M κ1 a1 := by
  have hκ0 : 0 < κ := lt_of_lt_of_le hκ1 hκ
  have ha10 : 0 ≤ a1 := ha.trans ha1
  unfold condF
  gcongr

theorem bndF_mono (p M : ℕ) {κ κ1 a a1 : ℝ} (hκ1 : 0 < κ1) (hκ : κ1 ≤ κ) (ha : 0 ≤ a) (ha1 : a ≤ a1) :
    bndF p M κ a ≤ bndF p M κ1 a1 := by
  have hκ0 : 0 < κ := lt_of_lt_of_le hκ1 hκ
  have ha10 : 0 ≤ a1 := ha.trans ha1
  unfold bndF
  gcongr

theorem errF_anti (p M : ℕ) {κ κ1 a a1 Pb : ℝ} (hκ1 : 0 < κ1) (hκ : κ1 ≤ κ) (ha : 0 ≤ a) (ha1 : a ≤ a1)
    (hP : 0 ≤ Pb) : errF p M κ a Pb ≤ errF p M κ1 a1 Pb := by
  have hκ0 : 0 < κ := lt_of_lt_of_le hκ1 hκ
  have ha10 : 0 ≤ a1 := ha.trans ha1
  have h1 := condF_anti p M hκ1 hκ ha ha1
  have h2 := bndF_mono p M hκ1 hκ ha ha1
  have hb0 : 0 ≤ bndF p M κ a := by unfold bndF; positivity
  have hc0 : 0 ≤ condF p M κ a := by unfold condF; positivity
  unfold errF
  gcongr

theorem smallF_anti (p M : ℕ) {κ κ1 a a1 Pb : ℝ} (hκ1 : 0 < κ1) (hκ : κ1 ≤ κ) (ha : 0 ≤ a) (ha1 : a ≤ a1) :
    smallF p M κ a Pb ≤ smallF p M κ1 a1 Pb := by
  have hκ0 : 0 < κ := lt_of_lt_of_le hκ1 hκ
  have ha10 : 0 ≤ a1 := ha.trans ha1
  unfold smallF
  gcongr

theorem kap_mono {e1 x1 z : ℝ} (he1 : 0 ≤ e1) (hx1 : e1 < x1) (hz : x1 ≤ z) :
    (x1 - e1) / (2 * x1) ≤ (z - e1) / (2 * z) := by
  have h0 : 0 < x1 := by linarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have := mul_le_mul_of_nonneg_left hz he1
  nlinarith

theorem disc_mono {x1 t y : ℝ} (hx1 : 1 ≤ x1) (ht : x1 ≤ t) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ((x1 + y - 1) ^ 2 - 4 * x1 * y) / (4 * x1) ≤ ((t + y - 1) ^ 2 - 4 * t * y) / (4 * t) := by
  have h0 : 0 < x1 := by linarith
  have ht0 : 0 < t := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hp : (y - 1) ^ 2 ≤ t * x1 := by
    have h1 : (y - 1) ^ 2 ≤ 1 := by nlinarith
    have h2 : 1 ≤ t * x1 := by nlinarith
    linarith
  have h := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hp)
  nlinarith [h]

/-- IVT root selection. -/
theorem root_select {c : ℝ → ℝ} {x1 y E : ℝ} (hx1 : 1 ≤ x1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hcont : ContinuousOn c (Set.Ici x1))
    (hQ : ∀ z, x1 ≤ z → |z * c z ^ 2 - (z + y - 1) * c z + y| ≤ E)
    (hdisc : E < ((x1 + y - 1) ^ 2 - 4 * x1 * y) / (4 * x1))
    (X : ℝ) (hX : x1 ≤ X) (hcX : c X < (X + y - 1) / (2 * X)) :
    ∀ z, x1 ≤ z → c z < (z + y - 1) / (2 * z) := by
  intro z hz
  by_contra hcon
  push_neg at hcon
  set D : ℝ → ℝ := fun t => c t - (t + y - 1) / (2 * t) with hD
  have hDc : ContinuousOn D (Set.uIcc z X) := by
    have hsub : Set.uIcc z X ⊆ Set.Ici x1 := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      show x1 ≤ t
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    refine (hcont.mono hsub).sub ?_
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => ?_)
    have := hsub ht
    have : x1 ≤ t := this
    linarith
  have h0 : (0 : ℝ) ∈ Set.uIcc (D z) (D X) := by
    rw [Set.mem_uIcc]; right
    exact ⟨by simp only [hD]; linarith, by simp only [hD]; linarith⟩
  obtain ⟨t, ht, hDt⟩ := intermediate_value_uIcc hDc h0
  have htx : x1 ≤ t := by
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have ht0 : 0 < t := by linarith
  have hct : c t = (t + y - 1) / (2 * t) := by simp only [hD] at hDt; linarith
  have hQt := hQ t htx
  rw [hct] at hQt
  have hval : t * ((t + y - 1) / (2 * t)) ^ 2 - (t + y - 1) * ((t + y - 1) / (2 * t)) + y =
      -(((t + y - 1) ^ 2 - 4 * t * y) / (4 * t)) := by
    field_simp; ring
  rw [hval, abs_neg] at hQt
  have hdm := disc_mono hx1 htx hy0 hy1
  have hpos : 0 ≤ ((t + y - 1) ^ 2 - 4 * t * y) / (4 * t) := by
    have hE0 : 0 ≤ E := (abs_nonneg _).trans (hQ x1 le_rfl)
    linarith
  rw [abs_of_nonneg hpos] at hQt
  linarith

/-- Closeness to the small root `g* = ψ - (1-y)/x` (other root `1 - ψ`), for `g` below the midpoint plus `η`. -/
theorem root_close {ψ y g E η : ℝ} (hψ0 : 0 < ψ) (hψ1 : ψ < 1) (hy0 : 0 ≤ y)
    (hΔ : 0 < (1 - ψ) - (ψ - (1 - y) / (1 / ψ + y / (1 - ψ))))
    (hη : η ≤ ((1 - ψ) - (ψ - (1 - y) / (1 / ψ + y / (1 - ψ)))) / 4)
    (hg : g < (1 / ψ + y / (1 - ψ) + y - 1) / (2 * (1 / ψ + y / (1 - ψ))) + η)
    (hQ : |(1 / ψ + y / (1 - ψ)) * g ^ 2 - (1 / ψ + y / (1 - ψ) + y - 1) * g + y| ≤ E) :
    |g - (ψ - (1 - y) / (1 / ψ + y / (1 - ψ)))| ≤
      4 * E / ((1 / ψ + y / (1 - ψ)) * ((1 - ψ) - (ψ - (1 - y) / (1 / ψ + y / (1 - ψ))))) := by
  set x := 1 / ψ + y / (1 - ψ) with hx
  have h1ψ : 0 < 1 - ψ := by linarith
  have hx0 : 0 < x := by rw [hx]; positivity
  set gs := ψ - (1 - y) / x with hgs
  set Δ := (1 - ψ) - gs with hΔdef
  have hψne : ψ ≠ 0 := hψ0.ne'
  have h1ψne : 1 - ψ ≠ 0 := h1ψ.ne'
  have hxg : x * gs = x * ψ - (1 - y) := by rw [hgs]; field_simp
  have hxp : x * ψ * (1 - ψ) = (1 - ψ) + y * ψ := by rw [hx]; field_simp
  have hfac : x * g ^ 2 - (x + y - 1) * g + y = x * (g - gs) * (g - (1 - ψ)) := by
    linear_combination (g - (1 - ψ)) * hxg - hxp
  have hmid : (x + y - 1) / (2 * x) = (gs + (1 - ψ)) / 2 := by
    rw [div_eq_div_iff (by positivity) two_ne_zero]
    linear_combination (-2) * hxg
  rw [hmid] at hg
  have hgap : Δ / 4 ≤ (1 - ψ) - g := by rw [hΔdef]; linarith
  have hgap0 : 0 < (1 - ψ) - g := by linarith
  rw [hfac, abs_mul, abs_mul, abs_of_pos hx0, abs_sub_comm g (1 - ψ), abs_of_pos hgap0] at hQ
  rw [le_div_iff₀ (by positivity)]
  have h2 : x * |g - gs| * (Δ / 4) ≤ x * |g - gs| * ((1 - ψ) - g) :=
    mul_le_mul_of_nonneg_left hgap (by positivity)
  have h3 : |g - gs| * (x * Δ) = 4 * (x * |g - gs| * (Δ / 4)) := by ring
  rw [h3]
  linarith

theorem quad_of_bias {z y c B : ℝ} (hc1 : c < 1) (hc0 : 0 ≤ c) (h : |z * c - y - c / (1 - c)| ≤ B) :
    |z * c ^ 2 - (z + y - 1) * c + y| ≤ B := by
  have h1 : 0 < 1 - c := by linarith
  have hid : z * c ^ 2 - (z + y - 1) * c + y = -((1 - c) * (z * c - y - c / (1 - c))) := by
    field_simp; ring
  rw [hid, abs_neg, abs_mul, abs_of_pos h1]
  have := abs_nonneg (z * c - y - c / (1 - c))
  nlinarith

/-- The mean normalized trace stays below the midpoint of the two roots, and nearly solves the quadratic. -/
theorem cbar_lt_mid [Fact Q2_moments] {M p : ℕ} (hM : 0 < M) (hpM : p ≤ M) {e1 x1 : ℝ} (he1 : 0 ≤ e1) (hx1 : e1 < x1)
    (hx11 : 1 ≤ x1)
    (hsmall : smallF p M ((x1 - e1) / (2 * x1)) (x1 - e1)⁻¹ (Pbad M p e1) ≤ (x1 - e1) / (2 * x1) / 2)
    (hdisc : biasErr p M x1 e1 (Pbad M p e1) <
      ((x1 + (p : ℝ) / M - 1) ^ 2 - 4 * x1 * ((p : ℝ) / M)) / (4 * x1)) :
    cbar M p x1 e1 < (x1 + (p : ℝ) / M - 1) / (2 * x1) ∧
      |x1 * cbar M p x1 e1 ^ 2 - (x1 + (p : ℝ) / M - 1) * cbar M p x1 e1 + (p : ℝ) / M| ≤
        biasErr p M x1 e1 (Pbad M p e1) := by
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hy0 : 0 ≤ (p : ℝ) / M := div_nonneg (Nat.cast_nonneg p) hMp.le
  have hy1 : (p : ℝ) / M ≤ 1 := by
    rw [div_le_one hMp]; exact_mod_cast hpM
  have hP0 : 0 ≤ Pbad M p e1 := by unfold Pbad; exact measureReal_nonneg
  have hκ1 : 0 < (x1 - e1) / (2 * x1) := div_pos (by linarith) (by linarith)
  have hQ : ∀ z, x1 ≤ z → |z * cbar M p z e1 ^ 2 - (z + (p : ℝ) / M - 1) * cbar M p z e1 + (p : ℝ) / M| ≤
      biasErr p M x1 e1 (Pbad M p e1) := by
    intro z hz
    have hk := kap_mono he1 hx1 hz
    have ha : (z - e1)⁻¹ ≤ (x1 - e1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    have ha0 : 0 ≤ (z - e1)⁻¹ := inv_nonneg.mpr (by linarith)
    have hs := smallF_anti p M (Pb := Pbad M p e1) hκ1 hk ha0 ha
    have hsz : (((M : ℝ)⁻¹) ^ 2 * (p * ((z - e1)⁻¹) ^ 2) + Pbad M p e1) / 2 +
        (M : ℝ)⁻¹ * ((z - e1)⁻¹ / ((z - e1) / (2 * z))) ≤ (z - e1) / (2 * z) / 2 := by
      have : smallF p M ((z - e1) / (2 * z)) (z - e1)⁻¹ (Pbad M p e1) ≤ (z - e1) / (2 * z) / 2 := by
        linarith
      exact this
    obtain ⟨hc0, hc1, hb⟩ := bias hM he1 (by linarith) hsz
    have hE := errF_anti p M (Pb := Pbad M p e1) hκ1 hk ha0 ha hP0
    rw [← biasErr_eq, ← biasErr_eq] at hE
    have hκz : 0 < (z - e1) / (2 * z) := lt_of_lt_of_le hκ1 hk
    exact quad_of_bias (by linarith) hc0 (hb.trans hE)
  have hcont := continuousOn_cbar M p hx1
  set X := x1 + e1 + 7 with hX
  have hXx : x1 ≤ X := by linarith
  have hcX : cbar M p X e1 < (X + (p : ℝ) / M - 1) / (2 * X) := by
    have h1 := cbar_le hM (p := p) (show e1 < X by linarith)
    have h2 : (X - e1)⁻¹ ≤ 1 / 8 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
    have h3 : (p : ℝ) / M * (X - e1)⁻¹ ≤ 1 * (1 / 8) :=
      mul_le_mul hy1 h2 (inv_nonneg.mpr (by linarith)) zero_le_one
    have h4 : 1 / 8 < (X + (p : ℝ) / M - 1) / (2 * X) := by
      rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  have hsel := root_select hx11 hy0 hy1 hcont hQ hdisc X hXx hcX
  exact ⟨hsel x1 le_rfl, hQ x1 le_rfl⟩

end Q2

end

-- ===== from Q2j.lean =====
section

namespace Q2

/-! PART (i), per-n pieces: the bad-event bound and the trace identity on the good event. -/

theorem Smat_eq_sampleCov {M p : ℕ} (X : Fin M → Fin p → ℂ) :
    Smat X = sampleCov M 1 (fun _ => 1) X := by
  rw [sampleCov_one_eq]
  unfold Smat dataMat
  congr 2
  · ext j k; simp
  · ext j k; simp

theorem Pbad_zero (M : ℕ) (e1 : ℝ) : Pbad M 0 e1 = 0 := by
  unfold Pbad
  have h : {X : Fin M → Fin 0 → ℂ | ¬ ((e1 : ℂ) • (1 : Matrix (Fin 0) (Fin 0) ℂ) - Smat X).PosSemidef} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    have h0 : ((e1 : ℂ) • (1 : Matrix (Fin 0) (Fin 0) ℂ) - Smat X) = 0 := by
      ext i; exact i.elim0
    rw [h0]; exact PosSemidef.zero
  rw [h, measureReal_empty]

theorem bad_subset {M p : ℕ} [NeZero p] (e1 : ℝ) :
    {X : Fin M → Fin p → ℂ | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef} ⊆
      {X | e1 < largestEig M 1 (fun _ => 1) X} := by
  intro X hX
  simp only [Set.mem_setOf_eq] at hX ⊢
  by_contra hle
  push_neg at hle
  apply hX
  rw [Smat_eq_sampleCov]
  exact (eig_le_iff_posSemidef (sampleCov_isHermitian M 1 (fun _ => 1) X) e1).mp
    ((largestEig_le_iff M 1 (fun _ => 1) X e1).mp hle)

/-- On the good event, `Re tr A / M - x ψ = x (F/M - g_e)` with `g_e = ψ - (1 - p/M)/x`. -/
theorem trA_good {M p : ℕ} (hM : 0 < M) {x e1 ψ : ℝ} (hx : e1 < x) (hx0 : 0 < x) (X : Fin M → Fin p → ℂ)
    (hg : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef) :
    (1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M -
      x * ψ = x * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) := by
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hS := (Smat_psd X).isHermitian
  have hSe := (eig_le_iff_posSemidef hS e1).mpr hg
  have hdet := unit_of_eig hS (fun j => by linarith [hSe j])
  have hT := trace_A (M := M) (p := p) (Matrix.of X)ᵀ (x : ℂ) hdet
  rw [hT]
  have hF : Ff x e1 X = resT x (Smat X) := by unfold Ff; rw [if_pos hg]
  rw [hF]
  unfold resT Smat
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.re_ofReal_mul]
  field_simp
  ring

end Q2

end

-- ===== from Q2k.lean =====
section

namespace Q2

/-! PART (i), per-n: root closeness with the `y`-parametrization (b) and the Chebyshev bound (d). -/

theorem Pbad_nonneg (M p : ℕ) (e1 : ℝ) : 0 ≤ Pbad M p e1 := by
  unfold Pbad; exact measureReal_nonneg

/-- (b): closeness of the mean normalized trace to `g_e = ψ - (1 - p/M)/x`. -/
theorem c_close [Fact Q2_moments] {M p : ℕ} (hM : 0 < M) (hpM : p ≤ M) {e1 ψ y x : ℝ} (hxd : x = 1 / ψ + y / (1 - ψ))
    (he1 : 0 ≤ e1) (hψ0 : 0 < ψ) (hψ1 : ψ < 1) (hy0 : 0 ≤ y) (hx : e1 < x) (hx1 : 1 ≤ x)
    (hsmall : smallF p M ((x - e1) / (2 * x)) (x - e1)⁻¹ (Pbad M p e1) ≤ (x - e1) / (2 * x) / 2)
    (hdisc : biasErr p M x e1 (Pbad M p e1) <
      ((x + (p : ℝ) / M - 1) ^ 2 - 4 * x * ((p : ℝ) / M)) / (4 * x))
    (hΔ : 0 < (1 - ψ) - (ψ - (1 - y) / x))
    (hη : |y - (p : ℝ) / M| / (2 * x) ≤ ((1 - ψ) - (ψ - (1 - y) / x)) / 4) :
    |cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)| ≤
      4 * (biasErr p M x e1 (Pbad M p e1) + |y - (p : ℝ) / M|) / (x * ((1 - ψ) - (ψ - (1 - y) / x))) +
        |y - (p : ℝ) / M| / x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hlt, hQe⟩ := cbar_lt_mid hM hpM he1 hx hx1 hsmall hdisc
  have hsm' := hsmall
  unfold smallF at hsm'
  obtain ⟨hc0, hc1, -⟩ := bias hM he1 hx hsm'
  have hκ : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
  set c := cbar M p x e1 with hc
  set B := biasErr p M x e1 (Pbad M p e1) with hB
  set ye := (p : ℝ) / M with hye
  have hc1' : c < 1 := by linarith
  have hQy : |x * c ^ 2 - (x + y - 1) * c + y| ≤ B + |y - ye| := by
    have hid : x * c ^ 2 - (x + y - 1) * c + y = (x * c ^ 2 - (x + ye - 1) * c + ye) + (y - ye) * (1 - c) := by
      ring
    rw [hid]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - c)]
    have h1 : |y - ye| * (1 - c) ≤ |y - ye| := by
      have := abs_nonneg (y - ye)
      nlinarith
    linarith
  have hg : c < (x + y - 1) / (2 * x) + |y - ye| / (2 * x) := by
    have hm : (x + ye - 1) / (2 * x) = (x + y - 1) / (2 * x) + (ye - y) / (2 * x) := by
      field_simp; ring
    have h2 : (ye - y) / (2 * x) ≤ |y - ye| / (2 * x) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have hrc := root_close (g := c) (E := B + |y - ye|) (η := |y - ye| / (2 * x)) hψ0 hψ1 hy0
    (by rw [← hxd]; exact hΔ) (by rw [← hxd]; exact hη) (by rw [← hxd]; exact hg) (by rw [← hxd]; exact hQy)
  rw [← hxd] at hrc
  have htri : |c - (ψ - (1 - ye) / x)| ≤ |c - (ψ - (1 - y) / x)| + |y - ye| / x := by
    have hd : (ψ - (1 - y) / x) - (ψ - (1 - ye) / x) = (y - ye) / x := by field_simp; ring
    have h3 : |(ψ - (1 - y) / x) - (ψ - (1 - ye) / x)| = |y - ye| / x := by
      rw [hd, abs_div, abs_of_pos hx0]
    have := abs_sub_le c (ψ - (1 - y) / x) (ψ - (1 - ye) / x)
    linarith
  linarith

theorem Ffd_bound {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (hx : e1 < x) (t : ℝ) (X : Fin M → Fin p → ℂ) :
    |Ff x e1 X / M - t| ≤ p * (x - e1)⁻¹ / M + |t| := by
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hF := abs_le.mp (Ff_bound hx X)
  have ht1 := le_abs_self t
  have ht2 := neg_abs_le t
  rw [abs_le]
  constructor
  · have h := div_le_div_of_nonneg_right hF.1 hMp.le
    rw [neg_div] at h
    linarith
  · have h := div_le_div_of_nonneg_right hF.2 hMp.le
    linarith

/-- (d): Chebyshev bound for the centred, rescaled trace. -/
theorem part1_n [Fact Q2_moments] {M p : ℕ} (hM : 0 < M) {x e1 ψ ε : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (hε : 0 < ε) :
    (SpikedWishart.SoftEdge.sampleLaw M p).real
      {X | ε < |Real.sqrt M * ((1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M -
          x * ψ)|} ≤
      Pbad M p e1 + 2 * x ^ 2 * ((condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) +
        M * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2) / ε ^ 2 := by
  have := isProb_law M p
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hx0 : 0 < x := lt_of_le_of_lt he1 hx
  have hsub : {X : Fin M → Fin p → ℂ | ε < |Real.sqrt M * ((1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M -
          x * ψ)|} ⊆
      {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef} ∪
        {X | ε ^ 2 ≤ M * x ^ 2 * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2} := by
    intro X hX
    by_cases hG : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef
    · right
      simp only [Set.mem_setOf_eq] at hX ⊢
      rw [trA_good hM hx hx0 X hG] at hX
      have h2 := pow_lt_pow_left₀ hX hε.le two_ne_zero
      rw [sq_abs, mul_pow, Real.sq_sqrt hMp.le] at h2
      have h3 : (M : ℝ) * (x * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x))) ^ 2 =
          M * x ^ 2 * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2 := by ring
      linarith
    · left; exact hG
  have hhm : Measurable (fun X : Fin M → Fin p → ℂ =>
      (M : ℝ) * x ^ 2 * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2) :=
    ((((measurable_Ff x e1).div_const _).sub_const _).pow_const 2).const_mul _
  have hhint : Integrable (fun X : Fin M → Fin p → ℂ =>
      (M : ℝ) * x ^ 2 * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2)
      (SpikedWishart.SoftEdge.sampleLaw M p) :=
    (iob2 (((measurable_Ff x e1).div_const _).sub_const _) _
      (Ffd_bound hM hx (ψ - (1 - (p : ℝ) / M) / x))).const_mul _
  have hcint : Integrable (fun X : Fin M → Fin p → ℂ => (Ff x e1 X / M - cbar M p x e1) ^ 2)
      (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob2 (((measurable_Ff x e1).div_const _).sub_const _) _ (Ffd_bound hM hx (cbar M p x e1))
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := SpikedWishart.SoftEdge.sampleLaw M p)
    (ae_of_all _ (fun X => by
      show (0 : ℝ) ≤ (M : ℝ) * x ^ 2 * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2
      positivity)) hhint (ε ^ 2)
  have hI1 : ∫ X, (Ff x e1 X / M - cbar M p x e1) ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p =
      (∫ X, (Ff x e1 X - ∫ Y, Ff x e1 Y ∂SpikedWishart.SoftEdge.sampleLaw M p) ^ 2
        ∂SpikedWishart.SoftEdge.sampleLaw M p) / (M : ℝ) ^ 2 := by
    rw [← integral_div]
    congr 1
    ext X
    unfold cbar
    rw [div_sub_div_same, div_pow]
  have hvar := var_Ff (p := p) hM he1 hx
  have hPb : Pbad M p e1 = (SpikedWishart.SoftEdge.sampleLaw M p).real
      {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef} := rfl
  rw [← hPb] at hvar
  have hint : ∫ X, (M : ℝ) * x ^ 2 * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2
      ∂SpikedWishart.SoftEdge.sampleLaw M p ≤
      2 * x ^ 2 * ((condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) +
        M * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2) := by
    have hpt : ∀ X : Fin M → Fin p → ℂ,
        (M : ℝ) * x ^ 2 * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2 ≤
        2 * M * x ^ 2 * (Ff x e1 X / M - cbar M p x e1) ^ 2 +
          2 * M * x ^ 2 * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2 := by
      intro X
      have hk : (0 : ℝ) ≤ M * x ^ 2 := by positivity
      have hsq := sq_nonneg ((Ff x e1 X / M - cbar M p x e1) - (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)))
      have hab : (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2 ≤
          2 * (Ff x e1 X / M - cbar M p x e1) ^ 2 + 2 * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2 := by
        nlinarith
      have := mul_le_mul_of_nonneg_left hab hk
      linarith
    have h2int : Integrable (fun X : Fin M → Fin p → ℂ => 2 * M * x ^ 2 * (Ff x e1 X / M - cbar M p x e1) ^ 2 +
        2 * M * x ^ 2 * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2)
        (SpikedWishart.SoftEdge.sampleLaw M p) := (hcint.const_mul _).add (integrable_const _)
    refine (integral_mono hhint h2int hpt).trans ?_
    rw [integral_add (hcint.const_mul (2 * M * x ^ 2))
      (integrable_const (2 * M * x ^ 2 * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2)),
      integral_const_mul, integral_const, probReal_univ, one_smul, hI1]
    have hM2 : (2 * M * x ^ 2) * ((∫ X, (Ff x e1 X - ∫ Y, Ff x e1 Y ∂SpikedWishart.SoftEdge.sampleLaw M p) ^ 2
        ∂SpikedWishart.SoftEdge.sampleLaw M p) / (M : ℝ) ^ 2) ≤
        (2 * M * x ^ 2) * ((M * (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1)) / (M : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hvar (by positivity)) (by positivity)
    have hM3 : (2 * M * x ^ 2) * ((M * (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1)) / (M : ℝ) ^ 2) =
        2 * x ^ 2 * (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) := by
      field_simp
    have hexp : 2 * x ^ 2 * ((condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) +
        M * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2) =
        2 * x ^ 2 * (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) +
          2 * M * x ^ 2 * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2 := by ring
    linarith [hM2, hM3]
  have hP2 : (SpikedWishart.SoftEdge.sampleLaw M p).real
      {X | ε ^ 2 ≤ M * x ^ 2 * (Ff x e1 X / M - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2} ≤
      2 * x ^ 2 * ((condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) +
        M * (cbar M p x e1 - (ψ - (1 - (p : ℝ) / M) / x)) ^ 2) / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  rw [← hPb]
  linarith

end Q2

end

-- ===== from Q2l.lean =====
section

namespace Q2

/-! PART (i), per-n with explicit constants: everything reduced to `M` and `Pb`. -/

theorem condF_p {p M : ℕ} (hpM : p ≤ M) {κ a : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) :
    condF p M κ a ≤ condF M M κ a := by
  have hpR : (p : ℝ) ≤ M := by exact_mod_cast hpM
  unfold condF
  gcongr

theorem bndF_p {p M : ℕ} (hpM : p ≤ M) {κ a : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) :
    bndF p M κ a ≤ bndF M M κ a := by
  have hpR : (p : ℝ) ≤ M := by exact_mod_cast hpM
  unfold bndF
  gcongr

theorem smallF_p {p M : ℕ} (hpM : p ≤ M) {κ a Pb : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) :
    smallF p M κ a Pb ≤ smallF M M κ a Pb := by
  have hpR : (p : ℝ) ≤ M := by exact_mod_cast hpM
  unfold smallF
  gcongr

theorem bndF_nonneg (p M : ℕ) {κ a : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) : 0 ≤ bndF p M κ a := by
  unfold bndF; positivity

theorem condF_nonneg (p M : ℕ) {κ a : ℝ} (hκ : 0 < κ) : 0 ≤ condF p M κ a := by
  unfold condF; positivity

theorem errF_p {p M : ℕ} (hpM : p ≤ M) {κ a Pb : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) (hP : 0 ≤ Pb) :
    errF p M κ a Pb ≤ errF M M κ a Pb := by
  have hpR : (p : ℝ) ≤ M := by exact_mod_cast hpM
  have h1 := condF_p hpM hκ ha
  have h2 := bndF_p hpM hκ ha
  have hb0 := bndF_nonneg p M hκ ha
  have hc0 := condF_nonneg p M (a := a) hκ
  unfold errF
  gcongr

theorem errF_nonneg (p M : ℕ) {κ a Pb : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) (hP : 0 ≤ Pb) : 0 ≤ errF p M κ a Pb := by
  have hb0 := bndF_nonneg p M hκ ha
  have hc0 := condF_nonneg p M (a := a) hκ
  unfold errF
  positivity

/-- Per-`n` bound for part (i), under explicit smallness conditions `E1`-`E5` (all `o(1)` as `M → ∞`). -/
theorem part1_det [Fact Q2_moments] {M p : ℕ} (hM : 0 < M) (hpM : p ≤ M) {C₀ ψ₀ δ y ψ ε x X0 κ1 a1 e1 : ℝ}
    (hψ₀ : 0 < ψ₀) (hδ : 0 < δ) (hy0 : 0 ≤ y) (hyC : |y - (p : ℝ) / M| ≤ C₀ / M) (hψa : ψ₀ ≤ ψ)
    (hψb : ψ ≤ (1 - δ) / (1 + Real.sqrt y)) (hε : 0 < ε)
    (hxd : x = 1 / ψ + y / (1 - ψ)) (hX0 : X0 = 1 / ψ₀ + (1 + C₀) / δ) (hκ1 : κ1 = δ ^ 2 / X0)
    (ha1 : a1 = 1 / (2 * δ ^ 2)) (he1 : e1 = (1 + Real.sqrt ((p : ℝ) / M)) ^ 2 + δ ^ 2)
    (E1 : Real.sqrt (C₀ / M) * (2 * (1 + Real.sqrt (1 + C₀)) + Real.sqrt (C₀ / M)) ≤ δ ^ 2)
    (E2 : C₀ / M ≤ δ / 2)
    (E3 : smallF M M κ1 a1 (Pbad M p e1) ≤ κ1 / 2)
    (E4 : errF M M κ1 a1 (Pbad M p e1) < δ ^ 2 / (8 * X0))
    (E5 : C₀ / M * (4 + C₀ + 2 * X0) ≤ δ ^ 2 / 2) :
    (SpikedWishart.SoftEdge.sampleLaw M p).real
      {X | ε < |Real.sqrt M * ((1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M -
          x * ψ)|} ≤
      Pbad M p e1 + 2 * X0 ^ 2 * ((condF M M κ1 a1 + bndF M M κ1 a1 ^ 2 * Pbad M p e1) +
        M * (4 * (errF M M κ1 a1 (Pbad M p e1) + C₀ / M) / δ + C₀ / M) ^ 2) / ε ^ 2 := by
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hC0 : 0 ≤ C₀ := by
    by_contra h
    push_neg at h
    have : C₀ / M < 0 := div_neg_of_neg_of_pos h hMp
    linarith [abs_nonneg (y - (p : ℝ) / M)]
  have hCMn : 0 ≤ C₀ / M := div_nonneg hC0 hMp.le
  set ye := (p : ℝ) / M with hye
  have hye0 : 0 ≤ ye := by positivity
  have hye1 : ye ≤ 1 := by rw [hye, div_le_one hMp]; exact_mod_cast hpM
  have hyy := abs_le.mp hyC
  have hCM : C₀ / M ≤ C₀ := div_le_self hC0 hM1
  have hy1 : y ≤ 1 + C₀ := by linarith [hyy.2]
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt y := ⟨_, rfl⟩
  rw [← hs] at hψb
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg y
  have hss : s ^ 2 = y := by rw [hs]; exact Real.sq_sqrt hy0
  have hψ0 : 0 < ψ := lt_of_lt_of_le hψ₀ hψa
  have hψs : ψ * (1 + s) ≤ 1 - δ := by rwa [le_div_iff₀ (by positivity)] at hψb
  have hψ1 : ψ ≤ 1 - δ := by
    have := mul_nonneg hψ0.le hs0
    linarith [hψs]
  have h1ψ : δ ≤ 1 - ψ := by linarith
  have h1ψ0 : 0 < 1 - ψ := by linarith
  have hψlt1 : ψ < 1 := by linarith
  have hx1 : 1 ≤ x := by
    rw [hxd]
    have h1 : 1 ≤ 1 / ψ := by rw [le_div_iff₀ hψ0]; linarith
    have h2 : 0 ≤ y / (1 - ψ) := div_nonneg hy0 h1ψ0.le
    linarith
  have hxX : x ≤ X0 := by
    rw [hxd, hX0]
    have h1 : 1 / ψ ≤ 1 / ψ₀ := one_div_le_one_div_of_le hψ₀ hψa
    have h2 : y / (1 - ψ) ≤ (1 + C₀) / δ := div_le_div₀ (by linarith) hy1 hδ h1ψ
    linarith
  have hx0 : 0 < x := by linarith
  have hX0pos : 0 < X0 := by linarith
  have hxp : x * ψ * (1 - ψ) = (1 - ψ) + y * ψ := by
    rw [hxd]; field_simp
    try ring
  have hxp' : x * ψ * (1 - ψ) = (1 - ψ) + s ^ 2 * ψ := by rw [hss]; exact hxp
  have hq0 : 0 < ψ * (1 - ψ) := mul_pos hψ0 h1ψ0
  have hF4 : 4 * δ ^ 2 ≤ x - (1 + s) ^ 2 := by
    have hN : (x - (1 + s) ^ 2) * (ψ * (1 - ψ)) = (1 - (1 + s) * ψ) ^ 2 := by
      linear_combination hxp'
    have hd : δ ≤ 1 - (1 + s) * ψ := by linarith [hψs]
    have hN2 : δ ^ 2 ≤ (1 - (1 + s) * ψ) ^ 2 := pow_le_pow_left₀ hδ.le hd 2
    have hq : ψ * (1 - ψ) ≤ 1 / 4 := by
      have h0 : ψ * (1 - ψ) = 1 / 4 - (ψ - 1 / 2) ^ 2 := by ring
      linarith [sq_nonneg (ψ - 1 / 2)]
    have h4 : 4 * δ ^ 2 * (ψ * (1 - ψ)) ≤ (x - (1 + s) ^ 2) * (ψ * (1 - ψ)) := by
      rw [hN]
      have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 4 * δ ^ 2)
      linarith
    exact le_of_mul_le_mul_right h4 hq0
  have hF5 : δ ≤ x * (1 - 2 * ψ) + 1 - y := by
    have hN : (x * (1 - 2 * ψ) + 1 - y) * (ψ * (1 - ψ)) = (1 - ψ - s * ψ) * (1 - ψ + s * ψ) := by
      rw [← hss]; linear_combination (1 - 2 * ψ) * hxp'
    have hd1 : δ ≤ 1 - ψ - s * ψ := by linarith [hψs]
    have hd2 : 1 - ψ ≤ 1 - ψ + s * ψ := by
      have := mul_nonneg hs0 hψ0.le
      linarith
    have h5 : δ * (ψ * (1 - ψ)) ≤ (x * (1 - 2 * ψ) + 1 - y) * (ψ * (1 - ψ)) := by
      rw [hN]
      have h6 : δ * (1 - ψ) ≤ (1 - ψ - s * ψ) * (1 - ψ + s * ψ) :=
        mul_le_mul hd1 hd2 h1ψ0.le (by linarith)
      have h7 : δ * (ψ * (1 - ψ)) ≤ δ * (1 - ψ) := by
        have : ψ * (1 - ψ) ≤ 1 - ψ := by
          have := mul_le_mul_of_nonneg_left hψlt1.le h1ψ0.le
          linarith
        exact mul_le_mul_of_nonneg_left this hδ.le
      linarith
    exact le_of_mul_le_mul_right h5 hq0
  have hdisc_y : (x + y - 1) ^ 2 - 4 * x * y = (x * (1 - 2 * ψ) + 1 - y) ^ 2 := by
    linear_combination 4 * x * hxp
  obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (C₀ / M) := ⟨_, rfl⟩
  rw [← ht] at E1
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
  have htt : t ^ 2 = C₀ / M := by rw [ht]; exact Real.sq_sqrt hCMn
  have hsqe : Real.sqrt ye ≤ s + t := by
    have h1 : ye ≤ (s + t) ^ 2 := by
      have h0 : (s + t) ^ 2 = s ^ 2 + t ^ 2 + 2 * (s * t) := by ring
      have := mul_nonneg hs0 ht0
      linarith [hyy.1]
    calc Real.sqrt ye ≤ Real.sqrt ((s + t) ^ 2) := Real.sqrt_le_sqrt h1
      _ = s + t := Real.sqrt_sq (by positivity)
  have hs1 : s ≤ Real.sqrt (1 + C₀) := by rw [hs]; exact Real.sqrt_le_sqrt hy1
  have he1x : 2 * δ ^ 2 ≤ x - e1 := by
    rw [he1]
    have h1 : 1 + Real.sqrt ye ≤ 1 + s + t := by linarith
    have h2 : (1 + Real.sqrt ye) ^ 2 ≤ (1 + s + t) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (1 + s + t) ^ 2 = (1 + s) ^ 2 + t * (2 * (1 + s) + t) := by ring
    have h4 : t * (2 * (1 + s) + t) ≤ t * (2 * (1 + Real.sqrt (1 + C₀)) + t) := by gcongr
    linarith [E1]
  have he10 : 0 ≤ e1 := by rw [he1]; positivity
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hex : e1 < x := by linarith
  have hκ1pos : 0 < κ1 := by rw [hκ1]; positivity
  have hκ1le : κ1 ≤ (x - e1) / (2 * x) := by
    rw [hκ1, div_le_div_iff₀ hX0pos (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hxX (by positivity : (0 : ℝ) ≤ 2 * δ ^ 2)
    have h2 := mul_le_mul_of_nonneg_right he1x hX0pos.le
    linarith
  have ha0 : 0 ≤ (x - e1)⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1le : (x - e1)⁻¹ ≤ a1 := by
    rw [ha1, one_div]; exact inv_anti₀ (by positivity) he1x
  have ha10 : 0 ≤ a1 := ha0.trans ha1le
  have hP0 := Pbad_nonneg M p e1
  have hsmall : smallF p M ((x - e1) / (2 * x)) (x - e1)⁻¹ (Pbad M p e1) ≤ (x - e1) / (2 * x) / 2 :=
    ((smallF_anti p M hκ1pos hκ1le ha0 ha1le).trans (smallF_p hpM hκ1pos ha10)).trans
      (E3.trans (by linarith))
  have hB : biasErr p M x e1 (Pbad M p e1) ≤ errF M M κ1 a1 (Pbad M p e1) := by
    rw [biasErr_eq]
    exact (errF_anti p M hκ1pos hκ1le ha0 ha1le hP0).trans (errF_p hpM hκ1pos ha10 hP0)
  have hdisc : biasErr p M x e1 (Pbad M p e1) < ((x + ye - 1) ^ 2 - 4 * x * ye) / (4 * x) := by
    have hdd : |((x + ye - 1) ^ 2 - 4 * x * ye) - ((x + y - 1) ^ 2 - 4 * x * y)| ≤
        C₀ / M * (4 + C₀ + 2 * X0) := by
      have hid : ((x + ye - 1) ^ 2 - 4 * x * ye) - ((x + y - 1) ^ 2 - 4 * x * y) =
          (ye - y) * (ye + y - 2 - 2 * x) := by ring
      rw [hid, abs_mul]
      have h1 : |ye - y| ≤ C₀ / M := by rw [abs_sub_comm]; exact hyC
      have h2 : |ye + y - 2 - 2 * x| ≤ 4 + C₀ + 2 * X0 := by
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul h1 h2 (abs_nonneg _) hCMn
    have hdy : δ ^ 2 ≤ (x + y - 1) ^ 2 - 4 * x * y := by
      rw [hdisc_y]; exact pow_le_pow_left₀ hδ.le hF5 2
    have hde : δ ^ 2 / 2 ≤ (x + ye - 1) ^ 2 - 4 * x * ye := by
      have := (abs_le.mp hdd).1
      linarith [E5]
    have h8 : δ ^ 2 / (8 * X0) ≤ ((x + ye - 1) ^ 2 - 4 * x * ye) / (4 * x) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left hxX (by positivity : (0 : ℝ) ≤ 4 * δ ^ 2)
      have h2 := mul_le_mul_of_nonneg_right hde (by positivity : (0 : ℝ) ≤ 8 * X0)
      linarith
    linarith [hB, E4]
  have hxΔ : δ ≤ x * ((1 - ψ) - (ψ - (1 - y) / x)) := by
    have h : x * ((1 - ψ) - (ψ - (1 - y) / x)) = x * (1 - 2 * ψ) + 1 - y := by
      field_simp
      try ring
    rw [h]; exact hF5
  have hΔ : 0 < (1 - ψ) - (ψ - (1 - y) / x) := pos_of_mul_pos_right (lt_of_lt_of_le hδ hxΔ) hx0.le
  have hη : |y - ye| / (2 * x) ≤ ((1 - ψ) - (ψ - (1 - y) / x)) / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : |y - ye| * 4 ≤ 2 * δ := by linarith [hyC, E2]
    have h2 : ((1 - ψ) - (ψ - (1 - y) / x)) * (2 * x) = 2 * (x * ((1 - ψ) - (ψ - (1 - y) / x))) := by ring
    linarith [hxΔ]
  have hcc := c_close hM hpM hxd he10 hψ0 hψlt1 hy0 hex hx1 hsmall hdisc hΔ hη
  have hG0 := errF_nonneg M M (Pb := Pbad M p e1) hκ1pos ha10 hP0
  have hH : |cbar M p x e1 - (ψ - (1 - ye) / x)| ≤
      4 * (errF M M κ1 a1 (Pbad M p e1) + C₀ / M) / δ + C₀ / M := by
    refine hcc.trans ?_
    have h1 : 4 * (biasErr p M x e1 (Pbad M p e1) + |y - ye|) / (x * ((1 - ψ) - (ψ - (1 - y) / x))) ≤
        4 * (errF M M κ1 a1 (Pbad M p e1) + C₀ / M) / δ :=
      div_le_div₀ (by positivity) (by linarith [hB, hyC]) hδ hxΔ
    have h2 : |y - ye| / x ≤ C₀ / M := (div_le_self (abs_nonneg _) hx1).trans hyC
    linarith
  have hpn := part1_n (p := p) (ψ := ψ) hM he10 hex hε
  have hcondC : condC p M x e1 ≤ condF M M κ1 a1 :=
    (condF_anti p M hκ1pos hκ1le ha0 ha1le).trans (condF_p hpM hκ1pos ha10)
  have hbnd : bnd0 p M x e1 ≤ bndF M M κ1 a1 :=
    (bndF_mono p M hκ1pos hκ1le ha0 ha1le).trans (bndF_p hpM hκ1pos ha10)
  have hbnd0 : 0 ≤ bnd0 p M x e1 := bndF_nonneg p M (lt_of_lt_of_le hκ1pos hκ1le) ha0
  have hsq : (cbar M p x e1 - (ψ - (1 - ye) / x)) ^ 2 ≤
      (4 * (errF M M κ1 a1 (Pbad M p e1) + C₀ / M) / δ + C₀ / M) ^ 2 :=
    sq_le_sq' (abs_le.mp hH).1 (abs_le.mp hH).2
  have hx2 : x ^ 2 ≤ X0 ^ 2 := pow_le_pow_left₀ hx0.le hxX 2
  have hA : condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1 ≤
      condF M M κ1 a1 + bndF M M κ1 a1 ^ 2 * Pbad M p e1 :=
    add_le_add hcondC (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbnd0 hbnd 2) hP0)
  have hIn : (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) +
      M * (cbar M p x e1 - (ψ - (1 - ye) / x)) ^ 2 ≤
      (condF M M κ1 a1 + bndF M M κ1 a1 ^ 2 * Pbad M p e1) +
        M * (4 * (errF M M κ1 a1 (Pbad M p e1) + C₀ / M) / δ + C₀ / M) ^ 2 :=
    add_le_add hA (mul_le_mul_of_nonneg_left hsq hMp.le)
  have hIn0 : 0 ≤ (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) +
      M * (cbar M p x e1 - (ψ - (1 - ye) / x)) ^ 2 :=
    add_nonneg (add_nonneg (condC_nonneg p M x e1) (mul_nonneg (sq_nonneg _) hP0))
      (mul_nonneg hMp.le (sq_nonneg _))
  have hfin : 2 * x ^ 2 * ((condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) +
      M * (cbar M p x e1 - (ψ - (1 - ye) / x)) ^ 2) ≤
      2 * X0 ^ 2 * ((condF M M κ1 a1 + bndF M M κ1 a1 ^ 2 * Pbad M p e1) +
        M * (4 * (errF M M κ1 a1 (Pbad M p e1) + C₀ / M) / δ + C₀ / M) ^ 2) :=
    mul_le_mul (by linarith) hIn hIn0 (by positivity)
  have hfin2 := div_le_div_of_nonneg_right hfin (sq_nonneg ε)
  linarith

end Q2

end

-- ===== from Q2m.lean =====
section

namespace Q2

/-! PART (i), limits (e): the per-`n` bound in the variables `u = 1/M`, `z = M³ Pb`, and part (i). -/

noncomputable def C1f (κ a : ℝ) : ℝ := 2 / κ ^ 2 * a ^ 4 + 8 * (a ^ 2) ^ 2 / κ ^ 4 * a ^ 2

noncomputable def PsiZ (κ a u z : ℝ) : ℝ :=
  4 / κ ^ 2 * ((a ^ 2 + u ^ 2 * z) / 2 + u ^ 2 * z + a / κ) +
    4 / κ ^ 3 * (4 * (a ^ 2 + u * (C1f κ a + z * (a + 2 * (u * a ^ 2) / κ) ^ 2) + u ^ 2 * z +
      u * (a / κ) ^ 2)) +
    (1 + 2 / κ) * (u ^ 2 * z)

noncomputable def bfun (κ a C₀ δ ε X0 u z : ℝ) : ℝ :=
  u ^ 3 * z + 2 * X0 ^ 2 * ((u * C1f κ a + u * z * (a + 2 * (u * a ^ 2) / κ) ^ 2) +
    u * (4 * (PsiZ κ a u z + C₀) / δ + C₀) ^ 2) / ε ^ 2

theorem condF_uz (M : ℕ) (hM : 0 < M) (κ a : ℝ) (hκ : κ ≠ 0) :
    condF M M κ a = (M : ℝ)⁻¹ * C1f κ a := by
  have hMp : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  unfold condF C1f
  field_simp
  try ring

theorem bndF_uz (M : ℕ) (hM : 0 < M) (κ a Pb : ℝ) (hκ : κ ≠ 0) :
    bndF M M κ a ^ 2 * Pb = (M : ℝ)⁻¹ * ((M : ℝ) ^ 3 * Pb) * (a + 2 * ((M : ℝ)⁻¹ * a ^ 2) / κ) ^ 2 := by
  have hMp : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  unfold bndF
  field_simp
  try ring

theorem errF_uz (M : ℕ) (hM : 0 < M) (κ a Pb : ℝ) (hκ : κ ≠ 0) :
    errF M M κ a Pb = (M : ℝ)⁻¹ * PsiZ κ a (M : ℝ)⁻¹ ((M : ℝ) ^ 3 * Pb) := by
  have hMp : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  unfold errF condF bndF PsiZ C1f
  field_simp
  try ring

theorem smallF_u (M : ℕ) (hM : 0 < M) (κ a Pb : ℝ) :
    smallF M M κ a Pb = ((M : ℝ)⁻¹ * a ^ 2 + Pb) / 2 + (M : ℝ)⁻¹ * (a / κ) := by
  have hMp : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  unfold smallF
  field_simp
  try ring

theorem bound_uz (M : ℕ) (hM : 0 < M) (κ a C₀ δ ε X0 Pb : ℝ) (hκ : κ ≠ 0) (hδ : δ ≠ 0) :
    Pb + 2 * X0 ^ 2 * ((condF M M κ a + bndF M M κ a ^ 2 * Pb) +
        M * (4 * (errF M M κ a Pb + C₀ / M) / δ + C₀ / M) ^ 2) / ε ^ 2 =
      bfun κ a C₀ δ ε X0 (M : ℝ)⁻¹ ((M : ℝ) ^ 3 * Pb) := by
  have hMp : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  rw [errF_uz M hM κ a Pb hκ, condF_uz M hM κ a hκ, bndF_uz M hM κ a Pb hκ]
  unfold bfun
  generalize PsiZ κ a (M : ℝ)⁻¹ ((M : ℝ) ^ 3 * Pb) = Ψ
  field_simp
  try ring

theorem continuous_PsiZ (κ a : ℝ) : Continuous (fun q : ℝ × ℝ => PsiZ κ a q.1 q.2) := by
  unfold PsiZ C1f
  fun_prop

theorem continuous_bfun (κ a C₀ δ ε X0 : ℝ) : Continuous (fun q : ℝ × ℝ => bfun κ a C₀ δ ε X0 q.1 q.2) := by
  unfold bfun
  have := continuous_PsiZ κ a
  fun_prop

theorem bfun_zero (κ a C₀ δ ε X0 : ℝ) : bfun κ a C₀ δ ε X0 0 0 = 0 := by
  unfold bfun; simp

theorem tendsto_PsiZ {u z : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) (hz : Tendsto z atTop (𝓝 0)) (κ a : ℝ) :
    Tendsto (fun n => PsiZ κ a (u n) (z n)) atTop (𝓝 (PsiZ κ a 0 0)) := by
  have h := ((continuous_PsiZ κ a).tendsto (0, 0)).comp (hu.prodMk_nhds hz)
  have e : PsiZ κ a (0, 0).1 (0, 0).2 = PsiZ κ a 0 0 := rfl
  rw [e] at h
  exact h

theorem tendsto_bfun {u z : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) (hz : Tendsto z atTop (𝓝 0))
    (κ a C₀ δ ε X0 : ℝ) : Tendsto (fun n => bfun κ a C₀ δ ε X0 (u n) (z n)) atTop (𝓝 0) := by
  have h := ((continuous_bfun κ a C₀ δ ε X0).tendsto (0, 0)).comp (hu.prodMk_nhds hz)
  have e : bfun κ a C₀ δ ε X0 (0, 0).1 (0, 0).2 = 0 := bfun_zero κ a C₀ δ ε X0
  rw [e] at h
  exact h

theorem z_tendsto [Fact P2_edgeRate] {M p : ℕ → ℕ} (hM : Tendsto M atTop atTop) (hpM : ∀ n, p n ≤ M n) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (M n : ℝ) ^ 3 * Pbad (M n) (p n) ((1 + Real.sqrt ((p n : ℝ) / M n)) ^ 2 + δ ^ 2))
      atTop (𝓝 0) := by
  have hE := (Fact.out : P2_edgeRate) (δ ^ 2) (by positivity) 3 M p hM hpM
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3) (Pbad_nonneg _ _ _)
  · refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Nat.cast_nonneg _) 3)
    have := isProb_law (M n) (p n)
    rcases Nat.eq_zero_or_pos (p n) with h0 | hpos
    · have hz : Pbad (M n) (p n) ((1 + Real.sqrt ((p n : ℝ) / M n)) ^ 2 + δ ^ 2) = 0 := by
        rw [h0]; exact Pbad_zero _ _
      rw [hz]; exact measureReal_nonneg
    · have : NeZero (p n) := ⟨by omega⟩
      unfold Pbad
      exact measureReal_mono (bad_subset _)

theorem part1_step [Fact Q2_moments] {M p : ℕ} (hM : 0 < M) (hpM : p ≤ M) {C₀ ψ₀ δ y ψ ε x X0 κ1 a1 e1 : ℝ}
    (hψ₀ : 0 < ψ₀) (hδ : 0 < δ) (hy0 : 0 ≤ y) (hyC : |y - (p : ℝ) / M| ≤ C₀ / M) (hψa : ψ₀ ≤ ψ)
    (hψb : ψ ≤ (1 - δ) / (1 + Real.sqrt y)) (hε : 0 < ε)
    (hxd : x = 1 / ψ + y / (1 - ψ)) (hX0 : X0 = 1 / ψ₀ + (1 + C₀) / δ) (hκ1 : κ1 = δ ^ 2 / X0)
    (hκ1p : 0 < κ1)
    (ha1 : a1 = 1 / (2 * δ ^ 2)) (he1 : e1 = (1 + Real.sqrt ((p : ℝ) / M)) ^ 2 + δ ^ 2)
    (E1 : Real.sqrt (C₀ / M) * (2 * (1 + Real.sqrt (1 + C₀)) + Real.sqrt (C₀ / M)) ≤ δ ^ 2)
    (E2 : C₀ / M ≤ δ / 2)
    (E3 : smallF M M κ1 a1 (Pbad M p e1) ≤ κ1 / 2)
    (E4 : errF M M κ1 a1 (Pbad M p e1) < δ ^ 2 / (8 * X0))
    (E5 : C₀ / M * (4 + C₀ + 2 * X0) ≤ δ ^ 2 / 2) :
    (SpikedWishart.SoftEdge.sampleLaw M p).real
      {X | ε < |Real.sqrt M * ((1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M -
          x * ψ)|} ≤ bfun κ1 a1 C₀ δ ε X0 (M : ℝ)⁻¹ ((M : ℝ) ^ 3 * Pbad M p e1) := by
  have h := part1_det hM hpM hψ₀ hδ hy0 hyC hψa hψb hε hxd hX0 hκ1 ha1 he1 E1 E2 E3 E4 E5
  rwa [bound_uz M hM κ1 a1 C₀ δ ε X0 _ hκ1p.ne' hδ.ne'] at h

/-- Part (i) of `Q2_resolvent`. -/
theorem part1 [Fact Q2_moments] [Fact P2_edgeRate] (C₀ ψ₀ δ : ℝ) (hψ₀ : 0 < ψ₀) (hδ : 0 < δ) (M p : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hpM : ∀ n, p n ≤ M n) (y ψ : ℕ → ℝ) (hy : ∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n)
    (hψ : ∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
      {X | ε < |Real.sqrt (M n) * ((1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((((1 / ψ n + y n / (1 - ψ n)) : ℝ) : ℂ) • 1 -
          (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M n -
          (1 / ψ n + y n / (1 - ψ n)) * ψ n)|}) atTop (𝓝 0) := by
  have hMr : Tendsto (fun n => (M n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hM
  have hu : Tendsto (fun n => (M n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hMr
  have hev1 : ∀ᶠ n in atTop, 1 ≤ M n := hM.eventually (eventually_ge_atTop 1)
  have hC0 : 0 ≤ C₀ := by
    obtain ⟨n, hn⟩ := hev1.exists
    have hMp : (0 : ℝ) < M n := Nat.cast_pos.mpr (by omega)
    by_contra h
    push_neg at h
    have := div_neg_of_neg_of_pos h hMp
    linarith [abs_nonneg (y n - (p n : ℝ) / M n), (hy n).2]
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℝ, X0 = 1 / ψ₀ + (1 + C₀) / δ := ⟨_, rfl⟩
  have hX0p : 0 < X0 := by
    have h1 : 0 < (1 + C₀) / δ := div_pos (by linarith) hδ
    have h2 : 0 < 1 / ψ₀ := one_div_pos.mpr hψ₀
    linarith
  obtain ⟨κ1, hκ1⟩ : ∃ κ1 : ℝ, κ1 = δ ^ 2 / X0 := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℝ, a1 = 1 / (2 * δ ^ 2) := ⟨_, rfl⟩
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hκ1p : 0 < κ1 := by rw [hκ1]; positivity
  have hz := z_tendsto hM hpM hδ
  have hw : Tendsto (fun n => C₀ / (M n : ℝ)) atTop (𝓝 0) := by
    have h := hu.const_mul C₀
    rw [mul_zero] at h
    exact h.congr (fun n => (div_eq_mul_inv _ _).symm)
  have hsw : Tendsto (fun n => Real.sqrt (C₀ / (M n : ℝ))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hw
    rwa [Real.sqrt_zero] at h
  -- E1
  have hE1 : ∀ᶠ n in atTop, Real.sqrt (C₀ / (M n : ℝ)) * (2 * (1 + Real.sqrt (1 + C₀)) +
      Real.sqrt (C₀ / (M n : ℝ))) ≤ δ ^ 2 := by
    have h := hsw.mul ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * (1 + Real.sqrt (1 + C₀))) atTop _).add hsw)
    rw [zero_mul] at h
    exact h.eventually (ge_mem_nhds hδ2)
  have hE2 : ∀ᶠ n in atTop, C₀ / (M n : ℝ) ≤ δ / 2 := hw.eventually (ge_mem_nhds (by linarith))
  have hE5 : ∀ᶠ n in atTop, C₀ / (M n : ℝ) * (4 + C₀ + 2 * X0) ≤ δ ^ 2 / 2 := by
    have h := hw.mul_const (4 + C₀ + 2 * X0)
    rw [zero_mul] at h
    exact h.eventually (ge_mem_nhds (by positivity))
  have hPs := tendsto_PsiZ hu hz κ1 a1
  have hE4 : ∀ᶠ n in atTop, errF (M n) (M n) κ1 a1
      (Pbad (M n) (p n) ((1 + Real.sqrt ((p n : ℝ) / M n)) ^ 2 + δ ^ 2)) < δ ^ 2 / (8 * X0) := by
    have h := hu.mul hPs
    rw [zero_mul] at h
    filter_upwards [h.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ 2 / (8 * X0))), hev1] with n hn hn1
    rw [errF_uz (M n) (by omega) κ1 a1 _ hκ1p.ne']
    exact hn
  have hPb0 : Tendsto (fun n => Pbad (M n) (p n) ((1 + Real.sqrt ((p n : ℝ) / M n)) ^ 2 + δ ^ 2))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
      (Eventually.of_forall (fun n => Pbad_nonneg _ _ _)) ?_
    filter_upwards [hev1] with n hn
    have hM1 : (1 : ℝ) ≤ (M n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
    exact le_mul_of_one_le_left (Pbad_nonneg _ _ _) hM1
  have hE3 : ∀ᶠ n in atTop, smallF (M n) (M n) κ1 a1
      (Pbad (M n) (p n) ((1 + Real.sqrt ((p n : ℝ) / M n)) ^ 2 + δ ^ 2)) ≤ κ1 / 2 := by
    have h := ((hu.mul_const (a1 ^ 2)).add hPb0).div_const 2 |>.add (hu.mul_const (a1 / κ1))
    simp only [zero_mul, zero_add, zero_div] at h
    filter_upwards [h.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < κ1 / 2)), hev1] with n hn hn1
    rw [smallF_u (M n) (by omega)]
    exact hn
  have hB := tendsto_bfun hu hz κ1 a1 C₀ δ ε X0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall (fun n => measureReal_nonneg)) ?_
  filter_upwards [hev1, hE1, hE2, hE3, hE4, hE5] with n hn h1 h2 h3 h4 h5
  have hMn : 0 < M n := by omega
  exact part1_step (M := M n) (p := p n) (x := 1 / ψ n + y n / (1 - ψ n)) hMn (hpM n) hψ₀ hδ
    (hy n).1 (hy n).2 (hψ n).1 (hψ n).2 hε rfl hX0 hκ1 hκ1p ha1 rfl h1 h2 h3 h4 h5

end Q2

end

-- ===== from QP1.lean =====
section

namespace Q2

theorem q2_part1_of : Q2_part1_of := by
  intro hMo hE
  have i1 : Fact Q2_moments := ⟨hMo⟩
  have i2 : Fact P2_edgeRate := ⟨hE⟩
  intro C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε hε
  exact part1 C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε hε

end Q2

end

end SpikedWishart.Separated.Lib

open SpikedWishart.Separated in
theorem solution :
  (∀ (M p : ℕ), 0 < M → ∀ (x e1 : ℝ), 0 ≤ e1 → e1 < x →
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
        ((p : ℝ) / M + 2 / κ) * Pb)) →
  (∀ (ε : ℝ), 0 < ε → ∀ (l : ℕ) (M N : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, N n ≤ M n) →
    Tendsto (fun n => (M n : ℝ) ^ l * (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X})
      atTop (𝓝 0)) →
  ∀ (C₀ ψ₀ δ : ℝ), 0 < ψ₀ → 0 < δ → ∀ (M p : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, p n ≤ M n) →
    ∀ (y ψ : ℕ → ℝ), (∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n) →
    (∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) →
    ∀ ε : ℝ, 0 < ε →
    let x : ℕ → ℝ := fun n => 1 / ψ n + y n / (1 - ψ n)
    let A : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n X =>
      1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x n : ℂ) • 1 - (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |Real.sqrt (M n) * ((((A n X).trace).re / M n) - x n * ψ n)|}) atTop (𝓝 0) := by
  exact SpikedWishart.Separated.Lib.Q2.q2_part1_of
