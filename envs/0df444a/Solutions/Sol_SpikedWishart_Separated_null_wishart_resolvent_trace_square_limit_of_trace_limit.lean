-- Prove2me | solution 1 for SpikedWishart.Separated.null_wishart_resolvent_trace_square_limit_of_trace_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:19:45.072824+00:00
-- url     : https://prove2.me/submissions/d6b57c72-a086-4685-bac0-279ff9bc2ce2

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

/-- Child: part (ii) from part (i) and the edge rate (convexity of `z ↦ tr A(z)/M`). -/
def Q2_part2_of : Prop := Q2_part1 → P2_edgeRate → Q2_part2

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

/-- Trace of `A²`. -/
theorem trace_A_sq {M p : ℕ} (Y : Matrix (Fin p) (Fin M) ℂ) (x : ℂ)
    (hdet : IsUnit (x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ)).det) :
    ((1 + (M : ℂ)⁻¹ • (Yᴴ * (x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ))⁻¹ * Y)) *
      (1 + (M : ℂ)⁻¹ • (Yᴴ * (x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ))⁻¹ * Y))).trace =
      M - p + x ^ 2 * (((x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ))⁻¹) *
        ((x • (1 : Matrix (Fin p) (Fin p) ℂ) - (M : ℂ)⁻¹ • (Y * Yᴴ))⁻¹)).trace := by
  set S := (M : ℂ)⁻¹ • (Y * Yᴴ) with hS
  set G := (x • (1 : Matrix (Fin p) (Fin p) ℂ) - S)⁻¹ with hG
  set B := (M : ℂ)⁻¹ • (Yᴴ * G * Y) with hB
  have hGS := G_mul_S S x hdet
  rw [← hG] at hGS
  have hB1 : B.trace = (G * S).trace := by
    simp only [hB, hS, Matrix.smul_mul, Matrix.mul_smul, trace_smul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Yᴴ]
    simp only [Matrix.mul_assoc]
  have hB2 : (B * B).trace = (G * S * (G * S)).trace := by
    simp only [hB, hS, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_smul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Yᴴ]
    simp only [Matrix.mul_assoc]
  have hsq : (1 + B) * (1 + B) = 1 + (2 : ℂ) • B + B * B := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      two_smul]
    abel
  rw [hsq, trace_add, trace_add, trace_smul, hB1, hB2, hGS]
  have e3 : (x • G - 1) * (x • G - 1) = (x ^ 2) • (G * G) - (2 * x) • G + 1 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, ← pow_two]
    rw [show (2 * x) • G = x • G + x • G by rw [two_mul, add_smul]]
    abel
  rw [e3, trace_sub, trace_add, trace_sub, trace_smul, trace_smul, trace_smul, trace_one, trace_one]
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

theorem Smat_psd {M p : ℕ} (X : Fin M → Fin p → ℂ) : (Smat X).PosSemidef := by
  have e : (M : ℂ)⁻¹ = (((M : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  unfold Smat
  rw [e]
  exact (posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.mpr (by positivity))

open Classical in
/-- Truncated trace `F = 1_{S <= e1} Re tr (x - S)⁻¹`. -/
noncomputable def Ff {M p : ℕ} (x e1 : ℝ) (X : Fin M → Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then resT x (Smat X) else 0

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

theorem isProb_law (M p : ℕ) : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw M p) := by
  have := Weyl.isProb_cg
  have hν : IsProbabilityMeasure (cgv p) := by unfold cgv; infer_instance
  show IsProbabilityMeasure (Measure.pi fun _ : Fin M => cgv p)
  infer_instance

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

end Q2

end

-- ===== from Q2l.lean =====
section

namespace Q2

/-! PART (i), per-n with explicit constants: everything reduced to `M` and `Pb`. -/

end Q2

end

-- ===== from Q2m.lean =====
section

namespace Q2

/-! PART (i), limits (e): the per-`n` bound in the variables `u = 1/M`, `z = M³ Pb`, and part (i). -/

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

/-- Part (i) of `Q2_resolvent`. -/
theorem part1 [Fact Q2_part1] (C₀ ψ₀ δ : ℝ) (hψ₀ : 0 < ψ₀) (hδ : 0 < δ) (M p : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hpM : ∀ n, p n ≤ M n) (y ψ : ℕ → ℝ) (hy : ∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n)
    (hψ : ∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
      {X | ε < |Real.sqrt (M n) * ((1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((((1 / ψ n + y n / (1 - ψ n)) : ℝ) : ℂ) • 1 -
          (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M n -
          (1 / ψ n + y n / (1 - ψ n)) * ψ n)|}) atTop (𝓝 0) := by
  exact (Fact.out : Q2_part1) C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε hε

end Q2

end

-- ===== from Q2n.lean =====
section

namespace Q2

/-! PART (ii), deterministic: convexity sandwich for `tr (x - S)⁻²` and the difference-quotient algebra. -/

theorem resT2_eq_sum {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) {x e1 : ℝ} (hx : e1 < x)
    (hKe : ∀ i, hK.eigenvalues i ≤ e1) : resT2 x K = ∑ i, ((x - hK.eigenvalues i)⁻¹) ^ 2 := by
  have hne : ∀ i, hK.eigenvalues i ≠ x := fun i => ne_of_lt (by linarith [hKe i])
  have h := res_diag hK x hne 2
  unfold resT2
  rw [← pow_two]
  exact h

theorem term_lo {d e : ℝ} (hd : 0 < d) (hde : d < e) : (d⁻¹ - e⁻¹) / (e - d) ≤ (d⁻¹) ^ 2 := by
  have he : 0 < e := by linarith
  have hed : e - d ≠ 0 := sub_ne_zero.mpr hde.ne'
  have h : (d⁻¹ - e⁻¹) / (e - d) = (d * e)⁻¹ := by
    field_simp
    try ring
  rw [h, inv_pow]
  apply inv_anti₀ (by positivity)
  rw [sq]
  exact mul_le_mul_of_nonneg_left hde.le hd.le

theorem term_hi {c d : ℝ} (hc : 0 < c) (hcd : c < d) : (d⁻¹) ^ 2 ≤ (c⁻¹ - d⁻¹) / (d - c) := by
  have hd : 0 < d := by linarith
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.ne'
  have h : (c⁻¹ - d⁻¹) / (d - c) = (c * d)⁻¹ := by
    field_simp
    try ring
  rw [h, inv_pow]
  apply inv_anti₀ (by positivity)
  rw [sq]
  exact mul_le_mul_of_nonneg_right hcd.le hd.le

theorem res_sandwich {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) {e1 xm x xp : ℝ}
    (hKe : ∀ i, hK.eigenvalues i ≤ e1) (h1 : e1 < xm) (h2 : xm < x) (h3 : x < xp) :
    (resT x K - resT xp K) / (xp - x) ≤ resT2 x K ∧ resT2 x K ≤ (resT xm K - resT x K) / (x - xm) := by
  have hx1 : e1 < x := by linarith
  have hxp1 : e1 < xp := by linarith
  rw [resT_eq_sum hK hx1 hKe, resT_eq_sum hK hxp1 hKe, resT_eq_sum hK h1 hKe,
    resT2_eq_sum hK hx1 hKe, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    Finset.sum_div, Finset.sum_div]
  constructor
  · refine Finset.sum_le_sum (fun i _ => ?_)
    have hl := hKe i
    have h := term_lo (d := x - hK.eigenvalues i) (e := xp - hK.eigenvalues i) (by linarith) (by linarith)
    rwa [show xp - hK.eigenvalues i - (x - hK.eigenvalues i) = xp - x by ring] at h
  · refine Finset.sum_le_sum (fun i _ => ?_)
    have hl := hKe i
    have h := term_hi (c := xm - hK.eigenvalues i) (d := x - hK.eigenvalues i) (by linarith) (by linarith)
    rwa [show x - hK.eigenvalues i - (xm - hK.eigenvalues i) = x - xm by ring] at h

theorem trA_re_good {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (hx : e1 < x) (hx0 : 0 < x) (X : Fin M → Fin p → ℂ)
    (hg : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef) :
    (1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M =
      x * (resT x (Smat X) / M) + (1 - (p : ℝ) / M) := by
  have h := trA_good (ψ := 0) hM hx hx0 X hg
  have hF : Ff x e1 X = resT x (Smat X) := by unfold Ff; rw [if_pos hg]
  rw [hF] at h
  have hx0' : x ≠ 0 := hx0.ne'
  have h2 : x * (resT x (Smat X) / M - (0 - (1 - (p : ℝ) / M) / x)) =
      x * (resT x (Smat X) / M) + (1 - (p : ℝ) / M) := by
    field_simp
    try ring
  linarith

theorem trA2_good {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (hx : e1 < x) (X : Fin M → Fin p → ℂ)
    (hg : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef) :
    ((1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)) *
      (1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ))).trace.re / M =
      (1 - (p : ℝ) / M) + x ^ 2 * (resT2 x (Smat X) / M) := by
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hS := (Smat_psd X).isHermitian
  have hSe := (eig_le_iff_posSemidef hS e1).mpr hg
  have hdet := unit_of_eig hS (fun j => by linarith [hSe j])
  have hT := trace_A_sq (M := M) (p := p) (Matrix.of X)ᵀ (x : ℂ) hdet
  rw [hT]
  unfold resT2 Smat
  rw [← Complex.ofReal_pow]
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.re_ofReal_mul]
  field_simp
  try ring

noncomputable def xof (y ψ : ℝ) : ℝ := 1 / ψ + y / (1 - ψ)

noncomputable def Wf (y ψ s : ℝ) : ℝ := 1 / (ψ * (ψ - s)) - y / ((1 - ψ) * (1 - ψ + s))

theorem xof_sub {y ψ s : ℝ} (hψ : ψ ≠ 0) (h1 : 1 - ψ ≠ 0) (h2 : ψ - s ≠ 0) (h3 : 1 - ψ + s ≠ 0) :
    xof y (ψ - s) - xof y ψ = s * Wf y ψ s := by
  have h4 : 1 - (ψ - s) ≠ 0 := by intro h; apply h3; linarith
  unfold xof Wf
  field_simp
  ring

theorem Wf_sub {y ψ s : ℝ} (hψ : ψ ≠ 0) (h1 : 1 - ψ ≠ 0) (h2 : ψ - s ≠ 0) (h3 : 1 - ψ + s ≠ 0) :
    Wf y ψ s - Wf y ψ 0 = s / (ψ ^ 2 * (ψ - s)) + y * s / ((1 - ψ) ^ 2 * (1 - ψ + s)) := by
  unfold Wf
  simp only [sub_zero, add_zero]
  field_simp
  ring

theorem Wf_zero (y ψ : ℝ) : Wf y ψ 0 = ψ⁻¹ ^ 2 - y / (1 - ψ) ^ 2 := by
  unfold Wf
  simp only [sub_zero, add_zero]
  ring

theorem T_alg {φ x xs W s ye : ℝ} (hx : x ≠ 0) (hxs : xs ≠ 0) (hs : s ≠ 0) (hW : W ≠ 0)
    (hd : xs - x = s * W) :
    1 - ye + x ^ 2 * (((φ - (1 - ye) / x) - ((φ - s) - (1 - ye) / xs)) / (xs - x)) =
      x ^ 2 / W + (1 - ye) * s * W / xs := by
  rw [hd]
  have hxs' : xs = x + s * W := by linarith
  subst hxs'
  field_simp
  ring

end Q2

end

-- ===== from Q2o.lean =====
section

namespace Q2

/-! PART (ii), deterministic core: from three approximate resolvent traces to the second moment. -/

theorem xof_ge_one {y φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hy0 : 0 ≤ y) : 1 ≤ xof y φ := by
  unfold xof
  have h1 : 1 ≤ 1 / φ := by rw [le_div_iff₀ hφ0]; linarith
  have h2 : 0 ≤ y / (1 - φ) := div_nonneg hy0 (by linarith)
  linarith

theorem Wdiff_bound {ψ y s' τ ψ₀ δ C₀ : ℝ} (hψ₀ : 0 < ψ₀) (hδ : 0 < δ) (hτ : 0 ≤ τ) (hs' : |s'| ≤ τ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 + C₀)
    (hD1 : ψ₀ ^ 3 / 2 ≤ ψ ^ 2 * (ψ - s')) (hD2 : δ ^ 3 / 2 ≤ (1 - ψ) ^ 2 * (1 - ψ + s')) :
    |s' / (ψ ^ 2 * (ψ - s')) + y * s' / ((1 - ψ) ^ 2 * (1 - ψ + s'))| ≤
      τ * (2 / ψ₀ ^ 3 + 2 * (1 + C₀) / δ ^ 3) := by
  have hP1 : 0 < ψ₀ ^ 3 / 2 := by positivity
  have hP2 : 0 < δ ^ 3 / 2 := by positivity
  have hQ1 : 0 < ψ ^ 2 * (ψ - s') := lt_of_lt_of_le hP1 hD1
  have hQ2 : 0 < (1 - ψ) ^ 2 * (1 - ψ + s') := lt_of_lt_of_le hP2 hD2
  have hC : 0 ≤ 1 + C₀ := le_trans hy0 hy1
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_div, abs_of_pos hQ1, abs_of_pos hQ2, abs_mul, abs_of_nonneg hy0]
  have h1 : |s'| / (ψ ^ 2 * (ψ - s')) ≤ τ / (ψ₀ ^ 3 / 2) := div_le_div₀ hτ hs' hP1 hD1
  have h2 : y * |s'| / ((1 - ψ) ^ 2 * (1 - ψ + s')) ≤ (1 + C₀) * τ / (δ ^ 3 / 2) :=
    div_le_div₀ (mul_nonneg hC hτ) (mul_le_mul hy1 hs' (abs_nonneg _) hC) hP2 hD2
  have e1 : τ / (ψ₀ ^ 3 / 2) = τ * (2 / ψ₀ ^ 3) := by field_simp
  have e2 : (1 + C₀) * τ / (δ ^ 3 / 2) = τ * (2 * (1 + C₀) / δ ^ 3) := by field_simp
  have e3 : τ * (2 / ψ₀ ^ 3 + 2 * (1 + C₀) / δ ^ 3) = τ * (2 / ψ₀ ^ 3) + τ * (2 * (1 + C₀) / δ ^ 3) := by ring
  linarith

theorem sq_div_diff {x X0 Wa W0 δ τK : ℝ} (hδ : 0 < δ) (hx0 : 0 ≤ x) (hxX : x ≤ X0) (hWa : δ / 2 ≤ Wa)
    (hW0 : δ ≤ W0) (hd : |Wa - W0| ≤ τK) :
    |x ^ 2 / Wa - x ^ 2 / W0| ≤ 2 * X0 ^ 2 * τK / δ ^ 2 := by
  have hWa0 : 0 < Wa := lt_of_lt_of_le (by positivity) hWa
  have hW00 : 0 < W0 := lt_of_lt_of_le hδ hW0
  have e : x ^ 2 / Wa - x ^ 2 / W0 = x ^ 2 * (W0 - Wa) / (Wa * W0) := by field_simp
  rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hWa0 hW00), abs_of_nonneg (sq_nonneg x), abs_sub_comm]
  have hτK : 0 ≤ τK := (abs_nonneg _).trans hd
  have hx2 : x ^ 2 ≤ X0 ^ 2 := pow_le_pow_left₀ hx0 hxX 2
  have hnum : x ^ 2 * |Wa - W0| ≤ X0 ^ 2 * τK := mul_le_mul hx2 hd (abs_nonneg _) (by positivity)
  have hden : δ / 2 * δ ≤ Wa * W0 := mul_le_mul hWa hW0 hδ.le hWa0.le
  have h := div_le_div₀ (by positivity) hnum (by positivity) hden
  have e2 : X0 ^ 2 * τK / (δ / 2 * δ) = 2 * X0 ^ 2 * τK / δ ^ 2 := by
    field_simp
    try ring
  linarith

theorem err_le {x X0 W δ τ ε' : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (hx0 : 0 ≤ x) (hxX : x ≤ X0) (hW : δ / 2 ≤ W)
    (hε' : 0 ≤ ε') : 2 * x ^ 2 * ε' / (τ * W) ≤ 4 * X0 ^ 2 * ε' / (τ * δ) := by
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hW
  have hx2 : x ^ 2 ≤ X0 ^ 2 := pow_le_pow_left₀ hx0 hxX 2
  have h := div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx2
    (by norm_num : (0 : ℝ) ≤ 2)) hε') (by positivity) (mul_le_mul_of_nonneg_left hW hτ.le)
  have e : 2 * X0 ^ 2 * ε' / (τ * (δ / 2)) = 4 * X0 ^ 2 * ε' / (τ * δ) := by
    field_simp
    try ring
  linarith

/-- The deterministic core of part (ii). -/
theorem part2_core {ψ y ye τ ε' h0 hm hp r2 δ ψ₀ C₀ X0 : ℝ}
    (hψ₀ : 0 < ψ₀) (hδ : 0 < δ) (hτ : 0 < τ) (hτψ : τ ≤ ψ₀ / 2) (hψa : ψ₀ ≤ ψ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 + C₀) (hψs : ψ * (1 + Real.sqrt y) ≤ 1 - δ)
    (hτs : τ * (1 + Real.sqrt y) ≤ δ / 2)
    (hye0 : 0 ≤ ye) (hye1 : ye ≤ 1) (hX0 : X0 = 1 / ψ₀ + (1 + C₀) / δ)
    (hτK : τ * (2 / ψ₀ ^ 3 + 2 * (1 + C₀) / δ ^ 3) ≤ δ / 2)
    (hlo : (h0 - hp) / (xof y (ψ - τ) - xof y ψ) ≤ r2) (hhi : r2 ≤ (hm - h0) / (xof y ψ - xof y (ψ + τ)))
    (ha0 : |h0 - (ψ - (1 - ye) / xof y ψ)| ≤ ε') (ham : |hm - ((ψ + τ) - (1 - ye) / xof y (ψ + τ))| ≤ ε')
    (hap : |hp - ((ψ - τ) - (1 - ye) / xof y (ψ - τ))| ≤ ε') :
    |(1 - ye) + xof y ψ ^ 2 * r2 - xof y ψ ^ 2 / (ψ⁻¹ ^ 2 - y / (1 - ψ) ^ 2)| ≤
      τ * (2 * X0 ^ 2 * (2 / ψ₀ ^ 3 + 2 * (1 + C₀) / δ ^ 3) / δ ^ 2 + 1 / ψ₀ ^ 2 + δ / 2) +
        4 * X0 ^ 2 * ε' / (τ * δ) := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt y := ⟨_, rfl⟩
  rw [← hs] at hψs hτs
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg y
  have hss : s ^ 2 = y := by rw [hs]; exact Real.sq_sqrt hy0
  have hε'0 : 0 ≤ ε' := (abs_nonneg _).trans ha0
  have hψ0 : 0 < ψ := lt_of_lt_of_le hψ₀ hψa
  have hψ1 : ψ ≤ 1 - δ := by
    have := mul_nonneg hψ0.le hs0
    linarith [hψs]
  have h1ψ : δ ≤ 1 - ψ := by linarith
  have h1ψ0 : 0 < 1 - ψ := by linarith
  have hψτ : ψ + τ ≤ 1 - δ / 2 := by
    have := mul_nonneg (add_pos hψ0 hτ).le hs0
    have e : (ψ + τ) * (1 + s) = ψ * (1 + s) + τ * (1 + s) := by ring
    linarith [hψs, hτs]
  have hψm : ψ₀ / 2 ≤ ψ - τ := by linarith
  have hψm0 : 0 < ψ - τ := by linarith
  set K := 2 / ψ₀ ^ 3 + 2 * (1 + C₀) / δ ^ 3 with hK
  obtain ⟨x, hx⟩ : ∃ x, x = xof y ψ := ⟨_, rfl⟩
  obtain ⟨xp, hxp⟩ : ∃ xp, xp = xof y (ψ - τ) := ⟨_, rfl⟩
  obtain ⟨xm, hxm⟩ : ∃ xm, xm = xof y (ψ + τ) := ⟨_, rfl⟩
  rw [← hx, ← hxp] at hlo
  rw [← hx, ← hxm] at hhi
  rw [← hx] at ha0
  rw [← hxm] at ham
  rw [← hxp] at hap
  rw [← hx]
  have hx1 : 1 ≤ x := by rw [hx]; exact xof_ge_one hψ0 (by linarith) hy0
  have hxp1 : 1 ≤ xp := by rw [hxp]; exact xof_ge_one hψm0 (by linarith) hy0
  have hxm1 : 1 ≤ xm := by rw [hxm]; exact xof_ge_one (by linarith) (by linarith) hy0
  have hxX : x ≤ X0 := by
    rw [hx, hX0]
    unfold xof
    have h1 : 1 / ψ ≤ 1 / ψ₀ := one_div_le_one_div_of_le hψ₀ hψa
    have h2 : y / (1 - ψ) ≤ (1 + C₀) / δ := div_le_div₀ (by linarith) hy1 hδ h1ψ
    linarith
  -- the three W values
  have hdp : xp - x = τ * Wf y ψ τ := by
    rw [hxp, hx]; exact xof_sub hψ0.ne' h1ψ0.ne' hψm0.ne' (by linarith : (0 : ℝ) < 1 - ψ + τ).ne'
  have hdm : xm - x = (-τ) * Wf y ψ (-τ) := by
    rw [hxm, hx, show ψ + τ = ψ - (-τ) by ring]
    exact xof_sub hψ0.ne' h1ψ0.ne' (by linarith : (0 : ℝ) < ψ - -τ).ne' (by linarith : (0 : ℝ) < 1 - ψ + -τ).ne'
  have hW0 : δ ≤ Wf y ψ 0 := by
    rw [Wf_zero]
    have hq : 0 < ψ ^ 2 * (1 - ψ) ^ 2 := by positivity
    have hN : (ψ⁻¹ ^ 2 - y / (1 - ψ) ^ 2) * (ψ ^ 2 * (1 - ψ) ^ 2) = (1 - ψ - s * ψ) * (1 - ψ + s * ψ) := by
      rw [← hss]; field_simp; ring
    have hd1 : δ ≤ 1 - ψ - s * ψ := by linarith [hψs]
    have hd2 : 1 - ψ ≤ 1 - ψ + s * ψ := by
      have := mul_nonneg hs0 hψ0.le
      linarith
    have h6 : δ * (1 - ψ) ≤ (1 - ψ - s * ψ) * (1 - ψ + s * ψ) := mul_le_mul hd1 hd2 h1ψ0.le (by linarith)
    have hψ2 : ψ ^ 2 * (1 - ψ) ≤ 1 := by
      have a1 : ψ ^ 2 ≤ 1 := pow_le_one₀ hψ0.le (by linarith)
      have a2 : 1 - ψ ≤ 1 := by linarith
      calc ψ ^ 2 * (1 - ψ) ≤ 1 * 1 := mul_le_mul a1 a2 h1ψ0.le (by norm_num)
        _ = 1 := by ring
    have h7 : δ * (ψ ^ 2 * (1 - ψ) ^ 2) ≤ δ * (1 - ψ) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      have e : ψ ^ 2 * (1 - ψ) ^ 2 = (ψ ^ 2 * (1 - ψ)) * (1 - ψ) := by ring
      rw [e]
      calc (ψ ^ 2 * (1 - ψ)) * (1 - ψ) ≤ 1 * (1 - ψ) := mul_le_mul_of_nonneg_right hψ2 h1ψ0.le
        _ = 1 - ψ := by ring
    have h8 : δ * (ψ ^ 2 * (1 - ψ) ^ 2) ≤ (ψ⁻¹ ^ 2 - y / (1 - ψ) ^ 2) * (ψ ^ 2 * (1 - ψ) ^ 2) := by
      rw [hN]; linarith
    exact le_of_mul_le_mul_right h8 hq
  have hW0u : Wf y ψ 0 ≤ 1 / ψ₀ ^ 2 := by
    rw [Wf_zero]
    have h1 : 0 ≤ y / (1 - ψ) ^ 2 := by positivity
    have h2 : ψ⁻¹ ≤ ψ₀⁻¹ := inv_anti₀ hψ₀ hψa
    have h3 : ψ⁻¹ ^ 2 ≤ ψ₀⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    have h4 : ψ₀⁻¹ ^ 2 = 1 / ψ₀ ^ 2 := by rw [inv_pow, one_div]
    linarith
  have hψτ1 : 0 < 1 - ψ + τ := by linarith
  have hψτ2 : δ / 2 ≤ 1 - ψ + -τ := by linarith
  have hdWp : |Wf y ψ τ - Wf y ψ 0| ≤ τ * K := by
    rw [Wf_sub hψ0.ne' h1ψ0.ne' hψm0.ne' hψτ1.ne']
    refine Wdiff_bound hψ₀ hδ hτ.le (by rw [abs_of_pos hτ]) hy0 hy1 ?_ ?_
    · have a1 : ψ₀ ^ 2 ≤ ψ ^ 2 := pow_le_pow_left₀ hψ₀.le hψa 2
      have a2 := mul_le_mul a1 hψm (by positivity) (by positivity)
      have e : ψ₀ ^ 3 / 2 = ψ₀ ^ 2 * (ψ₀ / 2) := by ring
      linarith
    · have a1 : δ ^ 2 ≤ (1 - ψ) ^ 2 := pow_le_pow_left₀ hδ.le h1ψ 2
      have a2 : δ / 2 ≤ 1 - ψ + τ := by linarith
      have a3 := mul_le_mul a1 a2 (by positivity) (by positivity)
      have e : δ ^ 3 / 2 = δ ^ 2 * (δ / 2) := by ring
      linarith
  have hdWm : |Wf y ψ (-τ) - Wf y ψ 0| ≤ τ * K := by
    rw [Wf_sub hψ0.ne' h1ψ0.ne' (by linarith : (0 : ℝ) < ψ - -τ).ne' (by linarith : (0 : ℝ) < 1 - ψ + -τ).ne']
    refine Wdiff_bound hψ₀ hδ hτ.le (by rw [abs_neg, abs_of_pos hτ]) hy0 hy1 ?_ ?_
    · have a1 : ψ₀ ^ 2 ≤ ψ ^ 2 := pow_le_pow_left₀ hψ₀.le hψa 2
      have a2 : ψ₀ / 2 ≤ ψ - -τ := by linarith
      have a3 := mul_le_mul a1 a2 (by positivity) (by positivity)
      have e : ψ₀ ^ 3 / 2 = ψ₀ ^ 2 * (ψ₀ / 2) := by ring
      linarith
    · have a1 : δ ^ 2 ≤ (1 - ψ) ^ 2 := pow_le_pow_left₀ hδ.le h1ψ 2
      have a3 := mul_le_mul a1 hψτ2 (by positivity) (by positivity)
      have e : δ ^ 3 / 2 = δ ^ 2 * (δ / 2) := by ring
      linarith
  have hWp : δ / 2 ≤ Wf y ψ τ := by linarith [(abs_le.mp hdWp).1]
  have hWm : δ / 2 ≤ Wf y ψ (-τ) := by linarith [(abs_le.mp hdWm).1]
  have hWpu : Wf y ψ τ ≤ 1 / ψ₀ ^ 2 + δ / 2 := by linarith [(abs_le.mp hdWp).2]
  have hWmu : Wf y ψ (-τ) ≤ 1 / ψ₀ ^ 2 + δ / 2 := by linarith [(abs_le.mp hdWm).2]
  have hWp0 : 0 < Wf y ψ τ := lt_of_lt_of_le (by positivity) hWp
  have hWm0 : 0 < Wf y ψ (-τ) := lt_of_lt_of_le (by positivity) hWm
  have hx0 : 0 < x := by linarith
  -- lower bound
  have ha0' := abs_le.mp ha0
  have ham' := abs_le.mp ham
  have hap' := abs_le.mp hap
  have hDp : 0 < xp - x := by rw [hdp]; positivity
  have hDm : 0 < x - xm := by
    have : x - xm = τ * Wf y ψ (-τ) := by linarith [hdm]
    rw [this]; positivity
  have hTp := T_alg (φ := ψ) (ye := ye) hx0.ne' (by linarith : (0 : ℝ) < xp).ne' hτ.ne' hWp0.ne' hdp
  have hTm := T_alg (φ := ψ) (ye := ye) hx0.ne' (by linarith : (0 : ℝ) < xm).ne' (neg_ne_zero.mpr hτ.ne') hWm0.ne' hdm
  rw [show ψ - -τ = ψ + τ by ring] at hTm
  have hlo2 : ((ψ - (1 - ye) / x) - ((ψ - τ) - (1 - ye) / xp)) / (xp - x) - 2 * ε' / (xp - x) ≤ r2 := by
    have h1 : ((ψ - (1 - ye) / x) - ((ψ - τ) - (1 - ye) / xp)) - 2 * ε' ≤ h0 - hp := by linarith
    have h2 := div_le_div_of_nonneg_right h1 hDp.le
    rw [sub_div] at h2
    linarith
  have hhi2 : r2 ≤ ((ψ - (1 - ye) / x) - ((ψ + τ) - (1 - ye) / xm)) / (xm - x) + 2 * ε' / (x - xm) := by
    have h1 : hm - h0 ≤ (((ψ + τ) - (1 - ye) / xm) - (ψ - (1 - ye) / x)) + 2 * ε' := by linarith
    have h2 := div_le_div_of_nonneg_right h1 hDm.le
    rw [add_div] at h2
    have e : (((ψ + τ) - (1 - ye) / xm) - (ψ - (1 - ye) / x)) / (x - xm) =
        ((ψ - (1 - ye) / x) - ((ψ + τ) - (1 - ye) / xm)) / (xm - x) := by
      rw [← neg_sub (ψ - (1 - ye) / x) ((ψ + τ) - (1 - ye) / xm), ← neg_sub xm x, neg_div_neg_eq]
    linarith
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hL := mul_le_mul_of_nonneg_left hlo2 hx2
  have hU := mul_le_mul_of_nonneg_left hhi2 hx2
  rw [mul_sub] at hL
  rw [mul_add] at hU
  -- error terms
  have hEp : x ^ 2 * (2 * ε' / (xp - x)) ≤ 4 * X0 ^ 2 * ε' / (τ * δ) := by
    have e : x ^ 2 * (2 * ε' / (xp - x)) = 2 * x ^ 2 * ε' / (τ * Wf y ψ τ) := by rw [hdp]; ring
    rw [e]; exact err_le hδ hτ hx0.le hxX hWp hε'0
  have hEm : x ^ 2 * (2 * ε' / (x - xm)) ≤ 4 * X0 ^ 2 * ε' / (τ * δ) := by
    have e : x ^ 2 * (2 * ε' / (x - xm)) = 2 * x ^ 2 * ε' / (τ * Wf y ψ (-τ)) := by
      have : x - xm = τ * Wf y ψ (-τ) := by linarith [hdm]
      rw [this]; ring
    rw [e]; exact err_le hδ hτ hx0.le hxX hWm hε'0
  -- main terms
  have hSp := sq_div_diff (x := x) hδ hx0.le hxX hWp hW0 hdWp
  have hSm := sq_div_diff (x := x) hδ hx0.le hxX hWm hW0 hdWm
  have hW0e : Wf y ψ 0 = ψ⁻¹ ^ 2 - y / (1 - ψ) ^ 2 := Wf_zero y ψ
  rw [hW0e] at hSp hSm
  have hcp : 0 ≤ (1 - ye) * τ * Wf y ψ τ / xp := by
    apply div_nonneg _ (by linarith)
    exact mul_nonneg (mul_nonneg (by linarith) hτ.le) hWp0.le
  have hcp2 : (1 - ye) * τ * Wf y ψ τ / xp ≤ τ * (1 / ψ₀ ^ 2 + δ / 2) := by
    rw [div_le_iff₀ (by linarith)]
    have a1 : (1 - ye) * τ * Wf y ψ τ ≤ 1 * τ * (1 / ψ₀ ^ 2 + δ / 2) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hτ.le) hWpu hWp0.le (by positivity)
    have a2 : τ * (1 / ψ₀ ^ 2 + δ / 2) ≤ τ * (1 / ψ₀ ^ 2 + δ / 2) * xp := by
      have : 0 ≤ τ * (1 / ψ₀ ^ 2 + δ / 2) := by positivity
      exact le_mul_of_one_le_right this hxp1
    linarith
  have hcm : 0 ≤ (1 - ye) * τ * Wf y ψ (-τ) / xm := by
    apply div_nonneg _ (by linarith)
    exact mul_nonneg (mul_nonneg (by linarith) hτ.le) hWm0.le
  have hTm' : 1 - ye + x ^ 2 * (((ψ - (1 - ye) / x) - ((ψ + τ) - (1 - ye) / xm)) / (xm - x)) =
      x ^ 2 / Wf y ψ (-τ) - (1 - ye) * τ * Wf y ψ (-τ) / xm := by
    rw [hTm]; ring
  have hSp' := abs_le.mp hSp
  have hSm' := abs_le.mp hSm
  have hτKX : τ * (2 * X0 ^ 2 * K / δ ^ 2 + 1 / ψ₀ ^ 2 + δ / 2) =
      2 * X0 ^ 2 * (τ * K) / δ ^ 2 + τ * (1 / ψ₀ ^ 2 + δ / 2) := by ring
  have hpos : 0 ≤ τ * (1 / ψ₀ ^ 2 + δ / 2) := by positivity
  rw [abs_le]
  constructor
  · linarith
  · linarith

end Q2

end

-- ===== from Q2p.lean =====
section

namespace Q2

/-! PART (ii), probabilistic assembly. -/

theorem edge_gap {M p : ℕ} (hM : 0 < M) (hpM : p ≤ M) {C₀ δ y ψ : ℝ} (hδ : 0 < δ) (hy0 : 0 ≤ y)
    (hyC : |y - (p : ℝ) / M| ≤ C₀ / M) (hψ0 : 0 < ψ) (hψs : ψ * (1 + Real.sqrt y) ≤ 1 - δ)
    (E1 : Real.sqrt (C₀ / M) * (2 * (1 + Real.sqrt (1 + C₀)) + Real.sqrt (C₀ / M)) ≤ δ ^ 2) :
    2 * δ ^ 2 ≤ xof y ψ - ((1 + Real.sqrt ((p : ℝ) / M)) ^ 2 + δ ^ 2) := by
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hC0 : 0 ≤ C₀ := by
    by_contra h
    push_neg at h
    have : C₀ / M < 0 := div_neg_of_neg_of_pos h hMp
    linarith [abs_nonneg (y - (p : ℝ) / M)]
  have hCMn : 0 ≤ C₀ / M := div_nonneg hC0 hMp.le
  set ye := (p : ℝ) / M with hye
  have hyy := abs_le.mp hyC
  have hCM : C₀ / M ≤ C₀ := div_le_self hC0 hM1
  have hy1 : y ≤ 1 + C₀ := by
    have hye1 : ye ≤ 1 := by rw [hye, div_le_one hMp]; exact_mod_cast hpM
    linarith [hyy.2]
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt y := ⟨_, rfl⟩
  rw [← hs] at hψs
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg y
  have hss : s ^ 2 = y := by rw [hs]; exact Real.sq_sqrt hy0
  have hψ1 : ψ ≤ 1 - δ := by
    have := mul_nonneg hψ0.le hs0
    linarith [hψs]
  have h1ψ0 : 0 < 1 - ψ := by linarith
  obtain ⟨x, hxd⟩ : ∃ x, x = xof y ψ := ⟨_, rfl⟩
  rw [← hxd]
  have hxp : x * ψ * (1 - ψ) = (1 - ψ) + y * ψ := by
    rw [hxd]; unfold xof; field_simp
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
  have h1 : 1 + Real.sqrt ye ≤ 1 + s + t := by linarith
  have h2 : (1 + Real.sqrt ye) ^ 2 ≤ (1 + s + t) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (1 + s + t) ^ 2 = (1 + s) ^ 2 + t * (2 * (1 + s) + t) := by ring
  have h4 : t * (2 * (1 + s) + t) ≤ t * (2 * (1 + Real.sqrt (1 + C₀)) + t) := by gcongr
  linarith [E1]

theorem xof_anti {y a b : ℝ} (ha : 0 < a) (hab : a < b) (hy : 0 ≤ y) (hb : b * (1 + Real.sqrt y) < 1) :
    xof y b < xof y a := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt y := ⟨_, rfl⟩
  rw [← hs] at hb
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg y
  have hss : s ^ 2 = y := by rw [hs]; exact Real.sq_sqrt hy
  have hb0 : 0 < b := by linarith
  have hsb : s * b < 1 - b := by linarith
  have h1b : 0 < 1 - b := lt_of_le_of_lt (mul_nonneg hs0 hb0.le) hsb
  have h1a : 0 < 1 - a := by linarith
  have hnum : 0 < (1 - a) * (1 - b) - y * a * b := by
    have e1 : (1 - b) * (1 - b) < (1 - a) * (1 - b) := mul_lt_mul_of_pos_right (by linarith) h1b
    have e2 : (s * b) * (s * b) ≤ (1 - b) * (1 - b) :=
      mul_le_mul hsb.le hsb.le (mul_nonneg hs0 hb0.le) h1b.le
    have e3 : y * a * b ≤ y * b * b := by
      have := mul_le_mul_of_nonneg_left hab.le (mul_nonneg hy hb0.le)
      linarith
    have e4 : (s * b) * (s * b) = y * b * b := by rw [← hss]; ring
    linarith
  have hid : xof y a - xof y b = (b - a) * ((1 - a) * (1 - b) - y * a * b) / (a * b * ((1 - a) * (1 - b))) := by
    unfold xof
    field_simp
    ring
  have hpos : 0 < (b - a) * ((1 - a) * (1 - b) - y * a * b) / (a * b * ((1 - a) * (1 - b))) := by
    apply div_pos (mul_pos (by linarith) hnum)
    positivity
  linarith

theorem approx_of_event {M p : ℕ} (hM : 0 < M) {x e1 φ ε' : ℝ} (he : e1 < x) (hx1 : 1 ≤ x)
    (X : Fin M → Fin p → ℂ) (hG : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef)
    (h : |Real.sqrt M * ((1 + (M : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x : ℂ) • 1 - (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)).trace.re / M -
          x * φ)| ≤ ε') :
    |resT x (Smat X) / M - (φ - (1 - (p : ℝ) / M) / x)| ≤ ε' := by
  have hx0 : 0 < x := by linarith
  rw [trA_re_good hM he hx0 X hG] at h
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hsq : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM1
  have e : x * (resT x (Smat X) / M) + (1 - (p : ℝ) / M) - x * φ =
      x * (resT x (Smat X) / M - (φ - (1 - (p : ℝ) / M) / x)) := by
    field_simp
    try ring
  rw [e, abs_mul, abs_mul, abs_of_pos hx0, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hD := abs_nonneg (resT x (Smat X) / M - (φ - (1 - (p : ℝ) / M) / x))
  have h1 : x * |resT x (Smat X) / M - (φ - (1 - (p : ℝ) / M) / x)| ≤
      Real.sqrt M * (x * |resT x (Smat X) / M - (φ - (1 - (p : ℝ) / M) / x)|) :=
    le_mul_of_one_le_left (by positivity) hsq
  have h2 : |resT x (Smat X) / M - (φ - (1 - (p : ℝ) / M) / x)| ≤
      x * |resT x (Smat X) / M - (φ - (1 - (p : ℝ) / M) / x)| := le_mul_of_one_le_left hD hx1
  linarith

end Q2

end

-- ===== from Q2q.lean =====
section

namespace Q2

/-! PART (ii): `(1/M) tr A² → x²/(ψ⁻² - y(1-ψ)⁻²)` in probability, and `Q2_resolvent`. -/

theorem meas_le_four {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {E A B C D : Set α}
    (h : ∀ x, x ∈ E → x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ D) :
    μ.real E ≤ μ.real A + (μ.real B + (μ.real C + μ.real D)) := by
  have hsub : E ⊆ A ∪ (B ∪ (C ∪ D)) := by
    intro x hx
    rcases h x hx with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  refine add_le_add le_rfl ((measureReal_union_le _ _).trans ?_)
  exact add_le_add le_rfl (measureReal_union_le _ _)

theorem part2 [Fact Q2_part1] [Fact P2_edgeRate] (C₀ ψ₀ δ : ℝ) (hψ₀ : 0 < ψ₀) (hδ : 0 < δ) (M p : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hpM : ∀ n, p n ≤ M n) (y ψ : ℕ → ℝ) (hy : ∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n)
    (hψ : ∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
      {X | ε < |((1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((((1 / ψ n + y n / (1 - ψ n)) : ℝ) : ℂ) • 1 -
          (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)) *
        (1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((((1 / ψ n + y n / (1 - ψ n)) : ℝ) : ℂ) • 1 -
          (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ))).trace.re / M n -
          (1 / ψ n + y n / (1 - ψ n)) ^ 2 / ((ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2)|}) atTop (𝓝 0) := by
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
  have hy1 : ∀ n, y n ≤ 1 + C₀ := by
    intro n
    have h := (hy n).2
    rcases Nat.eq_zero_or_pos (M n) with h0 | hpos
    · have hp0 : p n = 0 := by have := hpM n; omega
      rw [h0, hp0, Nat.cast_zero, div_zero, div_zero, sub_zero] at h
      have := le_abs_self (y n)
      linarith
    · have hMp : (0 : ℝ) < M n := Nat.cast_pos.mpr hpos
      have hM1 : (1 : ℝ) ≤ M n := by exact_mod_cast hpos
      have hye1 : (p n : ℝ) / M n ≤ 1 := by rw [div_le_one hMp]; exact_mod_cast hpM n
      have hCM : C₀ / M n ≤ C₀ := div_le_self hC0 hM1
      linarith [(abs_le.mp h).2]
  have hψs : ∀ n, ψ n * (1 + Real.sqrt (y n)) ≤ 1 - δ := fun n =>
    (le_div_iff₀ (by positivity)).mp (hψ n).2
  have hsy : ∀ n, Real.sqrt (y n) ≤ Real.sqrt (1 + C₀) := fun n => Real.sqrt_le_sqrt (hy1 n)
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℝ, X0 = 1 / ψ₀ + (1 + C₀) / δ := ⟨_, rfl⟩
  have hX0p : 0 < X0 := by
    have h1 : 0 < (1 + C₀) / δ := div_pos (by linarith) hδ
    have h2 : 0 < 1 / ψ₀ := one_div_pos.mpr hψ₀
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 / ψ₀ ^ 3 + 2 * (1 + C₀) / δ ^ 3 := ⟨_, rfl⟩
  have hKp : 0 < K := by
    rw [hK]
    have h1 : 0 < 1 + C₀ := by linarith
    positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * X0 ^ 2 * K / δ ^ 2 + 1 / ψ₀ ^ 2 + δ / 2 := ⟨_, rfl⟩
  have hLp : 0 < L := by rw [hL]; positivity
  have hS1 : 0 < 1 + Real.sqrt (1 + C₀) := by positivity
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = min (min (ψ₀ / 2) (δ / (2 * (1 + Real.sqrt (1 + C₀)))))
      (min (δ / (2 * K)) (ε / (2 * L))) := ⟨_, rfl⟩
  have hτp : 0 < τ := by
    rw [hτ]
    exact lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  have hτ1 : τ ≤ ψ₀ / 2 := by rw [hτ]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hτ2 : τ ≤ δ / (2 * (1 + Real.sqrt (1 + C₀))) := by
    rw [hτ]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hτ3 : τ ≤ δ / (2 * K) := by rw [hτ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hτ4 : τ ≤ ε / (2 * L) := by rw [hτ]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hτs : ∀ n, τ * (1 + Real.sqrt (y n)) ≤ δ / 2 := by
    intro n
    have h1 : τ * (2 * (1 + Real.sqrt (1 + C₀))) ≤ δ := (le_div_iff₀ (by positivity)).mp hτ2
    have h2 : τ * (1 + Real.sqrt (y n)) ≤ τ * (1 + Real.sqrt (1 + C₀)) :=
      mul_le_mul_of_nonneg_left (by linarith [hsy n]) hτp.le
    linarith
  have hτK : τ * K ≤ δ / 2 := by
    have h1 : τ * (2 * K) ≤ δ := (le_div_iff₀ (by positivity)).mp hτ3
    linarith
  have hτL : τ * L ≤ ε / 2 := by
    have h1 : τ * (2 * L) ≤ ε := (le_div_iff₀ (by positivity)).mp hτ4
    linarith
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε * τ * δ / (8 * X0 ^ 2) := ⟨_, rfl⟩
  have hε'p : 0 < ε' := by rw [hε']; positivity
  have hε'e : 4 * X0 ^ 2 * ε' / (τ * δ) = ε / 2 := by
    rw [hε']
    field_simp
    try ring
  -- the three part-(i) inputs
  have hPa := part1 C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε' hε'p
  have hPp := part1 C₀ (ψ₀ / 2) δ (half_pos hψ₀) hδ M p hM hpM y (fun n => ψ n - τ) hy
    (fun n => ⟨show ψ₀ / 2 ≤ ψ n - τ by linarith [(hψ n).1],
      show ψ n - τ ≤ (1 - δ) / (1 + Real.sqrt (y n)) from le_trans (by linarith) (hψ n).2⟩) ε' hε'p
  have hPm := part1 C₀ ψ₀ (δ / 2) hψ₀ (half_pos hδ) M p hM hpM y (fun n => ψ n + τ) hy
    (fun n => ⟨show ψ₀ ≤ ψ n + τ by linarith [(hψ n).1],
      show ψ n + τ ≤ (1 - δ / 2) / (1 + Real.sqrt (y n)) from (le_div_iff₀ (by positivity)).mpr (by
      have h1 := hψs n
      have h2 := hτs n
      linarith)⟩) ε' hε'p
  beta_reduce at hPp hPm
  -- the good event
  have hz := z_tendsto hM hpM (half_pos hδ)
  have hPb0 : Tendsto (fun n => Pbad (M n) (p n) ((1 + Real.sqrt ((p n : ℝ) / M n)) ^ 2 + (δ / 2) ^ 2))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
      (Eventually.of_forall (fun n => Pbad_nonneg _ _ _)) ?_
    filter_upwards [hev1] with n hn
    have hM1 : (1 : ℝ) ≤ (M n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
    exact le_mul_of_one_le_left (Pbad_nonneg _ _ _) hM1
  have hw : Tendsto (fun n => C₀ / (M n : ℝ)) atTop (𝓝 0) := by
    have h := hu.const_mul C₀
    rw [mul_zero] at h
    exact h.congr (fun n => (div_eq_mul_inv _ _).symm)
  have hsw : Tendsto (fun n => Real.sqrt (C₀ / (M n : ℝ))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hw
    rwa [Real.sqrt_zero] at h
  have hE1 : ∀ᶠ n in atTop, Real.sqrt (C₀ / (M n : ℝ)) * (2 * (1 + Real.sqrt (1 + C₀)) +
      Real.sqrt (C₀ / (M n : ℝ))) ≤ (δ / 2) ^ 2 := by
    have h := hsw.mul ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => 2 * (1 + Real.sqrt (1 + C₀))) atTop _).add hsw)
    rw [zero_mul] at h
    exact h.eventually (ge_mem_nhds (by positivity))
  have hsum := hPb0.add (hPa.add (hPp.add hPm))
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun n => measureReal_nonneg)) ?_
  filter_upwards [hev1, hE1] with n hn h1
  have hMn : 0 < M n := by omega
  have := isProb_law (M n) (p n)
  have hMp : (0 : ℝ) < M n := Nat.cast_pos.mpr hMn
  have hye0 : 0 ≤ (p n : ℝ) / M n := by positivity
  have hye1 : (p n : ℝ) / M n ≤ 1 := by rw [div_le_one hMp]; exact_mod_cast hpM n
  have hψ0 : 0 < ψ n := lt_of_lt_of_le hψ₀ (hψ n).1
  have hy0 := (hy n).1
  have hsq0 : 0 ≤ Real.sqrt (y n) := Real.sqrt_nonneg _
  have hψm : (ψ n + τ) * (1 + Real.sqrt (y n)) ≤ 1 - δ / 2 := by
    have h1 := hψs n
    have h2 := hτs n
    linarith
  have hgap := edge_gap hMn (hpM n) (half_pos hδ) hy0 (hy n).2 (by linarith) hψm h1
  have hxmx : xof (y n) (ψ n + τ) < xof (y n) (ψ n) :=
    xof_anti hψ0 (by linarith) hy0 (by linarith)
  have hxxp : xof (y n) (ψ n) < xof (y n) (ψ n - τ) := by
    have h3 := hψs n
    have h4 : 0 < ψ n - τ := by linarith [(hψ n).1]
    exact xof_anti h4 (by linarith) hy0 (by linarith)
  have hδ4 : 0 < 2 * (δ / 2) ^ 2 := by positivity
  have he1m : (1 + Real.sqrt ((p n : ℝ) / M n)) ^ 2 + (δ / 2) ^ 2 < xof (y n) (ψ n + τ) := by linarith
  have hx1 : 1 ≤ xof (y n) (ψ n) := xof_ge_one hψ0 (by
    have h3 := hψs n
    have := mul_nonneg hψ0.le hsq0
    linarith) hy0
  have hxm1 : 1 ≤ xof (y n) (ψ n + τ) := xof_ge_one (by linarith) (by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ ψ n + τ) hsq0
    linarith) hy0
  have hxp1 : 1 ≤ xof (y n) (ψ n - τ) := le_trans hx1 hxxp.le
  apply meas_le_four
  intro X hX
  by_contra hn
  simp only [not_or, Set.mem_setOf_eq, not_lt, not_not] at hn
  obtain ⟨hG, ha, hp', hm'⟩ := hn
  simp only [Set.mem_setOf_eq] at hX
  have A0 := approx_of_event hMn (x := xof (y n) (ψ n)) (φ := ψ n) (by linarith) hx1 X hG ha
  have Ap := approx_of_event hMn (x := xof (y n) (ψ n - τ)) (φ := ψ n - τ) (by linarith) hxp1 X hG hp'
  have Am := approx_of_event hMn (x := xof (y n) (ψ n + τ)) (φ := ψ n + τ) he1m hxm1 X hG hm'
  have hS := (Smat_psd X).isHermitian
  have hSe := (eig_le_iff_posSemidef hS _).mpr hG
  have hsw2 := res_sandwich hS hSe he1m hxmx hxxp
  have hlo : (resT (xof (y n) (ψ n)) (Smat X) / M n - resT (xof (y n) (ψ n - τ)) (Smat X) / M n) /
      (xof (y n) (ψ n - τ) - xof (y n) (ψ n)) ≤ resT2 (xof (y n) (ψ n)) (Smat X) / M n := by
    have h := div_le_div_of_nonneg_right hsw2.1 hMp.le
    have e : (resT (xof (y n) (ψ n)) (Smat X) - resT (xof (y n) (ψ n - τ)) (Smat X)) /
        (xof (y n) (ψ n - τ) - xof (y n) (ψ n)) / M n =
        (resT (xof (y n) (ψ n)) (Smat X) / M n - resT (xof (y n) (ψ n - τ)) (Smat X) / M n) /
        (xof (y n) (ψ n - τ) - xof (y n) (ψ n)) := by ring
    linarith
  have hhi : resT2 (xof (y n) (ψ n)) (Smat X) / M n ≤
      (resT (xof (y n) (ψ n + τ)) (Smat X) / M n - resT (xof (y n) (ψ n)) (Smat X) / M n) /
      (xof (y n) (ψ n) - xof (y n) (ψ n + τ)) := by
    have h := div_le_div_of_nonneg_right hsw2.2 hMp.le
    have e : (resT (xof (y n) (ψ n + τ)) (Smat X) - resT (xof (y n) (ψ n)) (Smat X)) /
        (xof (y n) (ψ n) - xof (y n) (ψ n + τ)) / M n =
        (resT (xof (y n) (ψ n + τ)) (Smat X) / M n - resT (xof (y n) (ψ n)) (Smat X) / M n) /
        (xof (y n) (ψ n) - xof (y n) (ψ n + τ)) := by ring
    linarith
  have core := part2_core (ye := (p n : ℝ) / M n) (X0 := X0) hψ₀ hδ hτp hτ1 (hψ n).1 hy0 (hy1 n)
    (hψs n) (hτs n) hye0 hye1 hX0 (by rw [← hK]; exact hτK) hlo hhi A0 Am Ap
  rw [← hK, ← hL] at core
  have core' : |(1 - (p n : ℝ) / M n) + (1 / ψ n + y n / (1 - ψ n)) ^ 2 *
      (resT2 (1 / ψ n + y n / (1 - ψ n)) (Smat X) / M n) -
      (1 / ψ n + y n / (1 - ψ n)) ^ 2 / ((ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2)| ≤
      τ * L + 4 * X0 ^ 2 * ε' / (τ * δ) := core
  have hA2 := trA2_good hMn (x := 1 / ψ n + y n / (1 - ψ n)) (by unfold xof at he1m hxmx; linarith) X hG
  rw [hA2] at hX
  linarith

end Q2

end

-- ===== from QP2.lean =====
section

namespace Q2

theorem q2_part2_of : Q2_part2_of := by
  intro hP1 hE
  have i1 : Fact Q2_part1 := ⟨hP1⟩
  have i2 : Fact P2_edgeRate := ⟨hE⟩
  intro C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε hε
  exact part2 C₀ ψ₀ δ hψ₀ hδ M p hM hpM y ψ hy hψ ε hε

end Q2

end

end SpikedWishart.Separated.Lib

open SpikedWishart.Separated in
theorem solution :
  (∀ (C₀ ψ₀ δ : ℝ), 0 < ψ₀ → 0 < δ → ∀ (M p : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, p n ≤ M n) →
    ∀ (y ψ : ℕ → ℝ), (∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n) →
    (∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) →
    ∀ ε : ℝ, 0 < ε →
    let x : ℕ → ℝ := fun n => 1 / ψ n + y n / (1 - ψ n)
    let A : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n X =>
      1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x n : ℂ) • 1 - (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |Real.sqrt (M n) * ((((A n X).trace).re / M n) - x n * ψ n)|}) atTop (𝓝 0)) →
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
        {X | ε < |((A n X * A n X).trace).re / M n -
          x n ^ 2 / ((ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2)|}) atTop (𝓝 0) := by
  exact SpikedWishart.Separated.Lib.Q2.q2_part2_of
