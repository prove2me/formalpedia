-- Prove2me | solution 1 for SpikedWishart.Separated.null_wishart_truncated_resolvent_trace_moments
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:19:45.071406+00:00
-- url     : https://prove2.me/submissions/60623528-3126-467c-a43d-ba3e7928dc5e

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

end

-- ===== from LamMax.lean =====
section

variable {k : ℕ}

/-- The Hermitian part `(H + Hᴴ)/2` of an array. -/
noncomputable def herm (H : Fin k → Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  (1 / 2 : ℂ) • (Matrix.of H + (Matrix.of H)ᴴ)

/-- The quadratic form, as a jointly continuous function. -/
noncomputable def quad (H : Fin k → Fin k → ℂ) (v : Fin k → ℂ) : ℝ := (star v ⬝ᵥ (herm H *ᵥ v)).re

theorem quad_smul (H : Fin k → Fin k → ℂ) (x : Fin k → ℂ) (a : ℝ) :
    quad H ((a : ℂ) • x) = a ^ 2 * quad H x := by
  unfold quad
  rw [mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im]
  ring

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

/-- `stdComplexGaussian` as a pushforward of two independent `N(0,1/2)`. -/
theorem integral_cg (f : ℂ → ℂ) (hf : AEStronglyMeasurable f SpikedWishart.SoftEdge.stdComplexGaussian) :
    ∫ z, f z ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      ∫ p, f ⟨p.1, p.2⟩ ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian at hf ⊢
  exact integral_map (φ := fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable hf

/-- Scalar characteristic function of the standard complex Gaussian. -/
theorem cg_char (a b : ℝ) :
    ∫ z, cexp (((a * z.re + b * z.im : ℝ) : ℂ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      cexp (-(((a ^ 2 + b ^ 2) / 4 : ℝ) : ℂ)) := by
  rw [integral_cg _ (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, cexp (((a * (⟨p.1, p.2⟩ : ℂ).re + b * (⟨p.1, p.2⟩ : ℂ).im : ℝ) : ℂ) * I) =
      cexp (a * p.1 * I) * cexp (b * p.2 * I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => cexp (a * x * I)) (fun y : ℝ => cexp (b * y * I))]
  rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `E exp(i t x²)` for `x ∼ N(0,1/2)`. -/
theorem g_sq_char (t : ℝ) :
    ∫ x, cexp ((t * x ^ 2 : ℝ) * I) ∂(gaussianReal 0 (1 / 2)) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h : ∀ x : ℝ, gaussianPDFReal 0 (1 / 2) x • cexp ((t * x ^ 2 : ℝ) * I) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * cexp (-(1 - t * I) * (x : ℂ) ^ 2) := by
    intro x
    rw [gaussianPDFReal, Complex.real_smul]
    have h2 : (2 * Real.pi * ((1 / 2 : NNReal) : ℝ)) = Real.pi := by push_cast; ring
    have h3 : (-(x - 0) ^ 2 / (2 * ((1 / 2 : NNReal) : ℝ))) = -x ^ 2 := by push_cast; ring
    have h4 : (((-x ^ 2 : ℝ)) : ℂ) + ((t * x ^ 2 : ℝ) : ℂ) * I = -(1 - t * I) * (x : ℂ) ^ 2 := by
      push_cast; ring
    rw [h2, h3, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv, mul_assoc,
      ← Complex.exp_add, h4]
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian_complex (by simp)]

/-- `E exp(i t |z|²) = 1/(1 - i t)` for the standard complex Gaussian. -/
theorem cg_normSq_char (t : ℝ) :
    ∫ z, cexp ((t * Complex.normSq z : ℝ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      1 / (1 - t * I) := by
  rw [integral_cg _ (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, cexp ((t * Complex.normSq (⟨p.1, p.2⟩ : ℂ) : ℝ) * I) =
      cexp ((t * p.1 ^ 2 : ℝ) * I) * cexp ((t * p.2 ^ 2 : ℝ) * I) := by
    intro p
    rw [← Complex.exp_add, Complex.normSq_mk]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => cexp ((t * x ^ 2 : ℝ) * I))
    (fun y : ℝ => cexp ((t * y ^ 2 : ℝ) * I)), g_sq_char]
  have hb : (1 - (t : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc : ((Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ)) ^ 2 = (Real.pi : ℂ) / (1 - t * I) := by
    rw [one_div, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_nat_inv_pow _ (by norm_num)]
  calc ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ) *
        (((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ))
      = (((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2)⁻¹ * ((Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ)) ^ 2 := by
        push_cast; ring
    _ = 1 / (1 - t * I) := by
        rw [hpi, hc]; field_simp

end

-- ===== from Q3b.lean =====
section

/-- Real Frobenius pairing `Re tr(Tᴴ Y)`, written entrywise. -/
noncomputable def pair {α β : Type*} [Fintype α] [Fintype β] (T Y : Matrix α β ℂ) : ℝ :=
  ∑ a, ∑ b, (star (T a b) * Y a b).re

theorem pair_eq_trace {α β : Type*} [Fintype α] [Fintype β] (T Y : Matrix α β ℂ) :
    pair T Y = (trace (Tᴴ * Y)).re := by
  simp only [pair, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]

theorem pair_self {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ) :
    pair T T = ∑ a, ∑ b, ((T a b).re ^ 2 + (T a b).im ^ 2) := by
  simp only [pair]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp [Complex.mul_re]
  ring

theorem eq_zero_of_pair_self {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ)
    (h : pair T T = 0) : T = 0 := by
  rw [pair_self] at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).mp h
  ext a b
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).mp
    (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
  have hr : (T a b).re = 0 := by nlinarith [sq_nonneg (T a b).re, sq_nonneg (T a b).im]
  have hi : (T a b).im = 0 := by nlinarith [sq_nonneg (T a b).re, sq_nonneg (T a b).im]
  exact Complex.ext (by simp [hr]) (by simp [hi])

/-- Characteristic function of the i.i.d. complex Gaussian array. -/
theorem sample_char (M N : ℕ) (τ : Matrix (Fin M) (Fin N) ℂ) :
    ∫ X, cexp ((pair τ (Matrix.of X) : ℂ) * I) ∂SpikedWishart.SoftEdge.sampleLaw M N =
      cexp (-((pair τ τ / 4 : ℝ) : ℂ)) := by
  have h1 : ∀ X : Fin M → Fin N → ℂ, cexp ((pair τ (Matrix.of X) : ℂ) * I) =
      ∏ m, ∏ j, cexp ((((τ m j).re * (X m j).re + (τ m j).im * (X m j).im : ℝ) : ℂ) * I) := by
    intro X
    simp only [pair, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl (fun m _ => Finset.prod_congr rfl (fun j _ => ?_))
    congr 3
    simp [Complex.mul_re]
  simp_rw [h1]
  unfold SpikedWishart.SoftEdge.sampleLaw
  rw [integral_fintype_prod_eq_prod (fun m (x : Fin N → ℂ) =>
    ∏ j, cexp ((((τ m j).re * (x j).re + (τ m j).im * (x j).im : ℝ) : ℂ) * I))]
  have h2 : ∀ m : Fin M, ∫ x : Fin N → ℂ, ∏ j, cexp ((((τ m j).re * (x j).re +
        (τ m j).im * (x j).im : ℝ) : ℂ) * I) ∂(Measure.pi fun _ => SpikedWishart.SoftEdge.stdComplexGaussian) =
      ∏ j, cexp (-((((τ m j).re ^ 2 + (τ m j).im ^ 2) / 4 : ℝ) : ℂ)) := by
    intro m
    rw [integral_fintype_prod_eq_prod (fun j (z : ℂ) =>
      cexp ((((τ m j).re * z.re + (τ m j).im * z.im : ℝ) : ℂ) * I))]
    exact Finset.prod_congr rfl (fun j _ => cg_char _ _)
  simp_rw [h2]
  rw [pair_self]
  simp only [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The pairing as an `ℝ`-bilinear map on arrays. -/
noncomputable def Lpair (M N : ℕ) :
    (Fin M → Fin N → ℂ) →ₗ[ℝ] (Fin M → Fin N → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => pair (Matrix.of w) (Matrix.of v))
    (fun v1 v2 w => by
      simp only [pair, Matrix.of_apply, Pi.add_apply, mul_add, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r v w => by
      simp only [pair, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Complex.real_smul]; simp [Complex.mul_re]; ring)
    (fun v w1 w2 => by
      simp only [pair, Matrix.of_apply, Pi.add_apply, star_add, add_mul, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r v w => by
      simp only [pair, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Complex.real_smul]; simp [Complex.mul_re]; ring)

theorem Lpair_apply (M N : ℕ) (v w : Fin M → Fin N → ℂ) :
    Lpair M N v w = pair (Matrix.of w) (Matrix.of v) := rfl

theorem continuous_Lpair (M N : ℕ) :
    Continuous fun p : (Fin M → Fin N → ℂ) × (Fin M → Fin N → ℂ) => Lpair M N p.1 p.2 := by
  simp only [Lpair_apply, pair, Matrix.of_apply]
  fun_prop

theorem continuous_pair_of {M N : ℕ} (T : Matrix (Fin M) (Fin N) ℂ) :
    Continuous (fun X : Fin M → Fin N → ℂ => pair T (Matrix.of X)) := by
  simp only [pair, Matrix.of_apply]
  fun_prop

theorem continuous_char_pair {M N : ℕ} (T : Matrix (Fin M) (Fin N) ℂ) :
    Continuous (fun X : Fin M → Fin N → ℂ => cexp ((pair T (Matrix.of X) : ℂ) * I)) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_pair_of T)).mul
    continuous_const)

theorem conjTranspose_map_star {α β : Type*} (Q : Matrix α β ℂ) : (Q.map star)ᴴ = Qᵀ := by
  ext i j; simp

theorem transpose_mul_map_star {α : Type*} [Fintype α] [DecidableEq α] (Q : Matrix α α ℂ)
    (hQ : Q ∈ unitaryGroup α ℂ) : Qᵀ * Q.map star = 1 := by
  have h := mem_unitaryGroup_iff'.mp hQ
  ext i j
  have := congrArg star (congrFun (congrFun h i) j)
  simp only [mul_apply, star_apply, Matrix.one_apply, transpose_apply, map_apply, star_sum,
    star_mul', star_star] at this ⊢
  rw [this]
  split_ifs <;> simp

theorem map_star_mul_transpose {α : Type*} [Fintype α] [DecidableEq α] (P : Matrix α α ℂ)
    (hP : P ∈ unitaryGroup α ℂ) : P.map star * Pᵀ = 1 := by
  have h := mem_unitaryGroup_iff.mp hP
  ext i j
  have := congrArg star (congrFun (congrFun h i) j)
  simp only [mul_apply, star_apply, Matrix.one_apply, transpose_apply, map_apply, star_sum,
    star_mul', star_star] at this ⊢
  rw [this]
  split_ifs <;> simp

/-- Moving a two-sided unitary action across the pairing. -/
theorem pair_unitary {M N : ℕ} (W Y : Matrix (Fin M) (Fin N) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (Q : Matrix (Fin M) (Fin M) ℂ) :
    pair W ((P * Yᵀ * Q)ᵀ) = pair (Q.map star * W * P.map star) Y := by
  rw [pair_eq_trace, pair_eq_trace]
  congr 1
  rw [transpose_mul, transpose_mul, transpose_transpose, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_map_star, conjTranspose_map_star]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

theorem pair_unitary_self {M N : ℕ} (W : Matrix (Fin M) (Fin N) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (Q : Matrix (Fin M) (Fin M) ℂ) (hP : P ∈ unitaryGroup (Fin N) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin M) ℂ) :
    pair (Q.map star * W * P.map star) (Q.map star * W * P.map star) = pair W W := by
  rw [pair_eq_trace, pair_eq_trace]
  congr 1
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_map_star, conjTranspose_map_star]
  have e : Pᵀ * (Wᴴ * Qᵀ) * (Q.map star * W * P.map star) =
      Pᵀ * (Wᴴ * (Qᵀ * Q.map star) * W) * P.map star := by
    simp only [Matrix.mul_assoc]
  rw [e, transpose_mul_map_star Q hQ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    map_star_mul_transpose P hP, Matrix.one_mul]

/-- Unitary invariance of the i.i.d. complex Gaussian array under `H ↦ P H Q`
(`H = (of X)ᵀ`). -/
theorem sample_invariant (M N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ) (Q : Matrix (Fin M) (Fin M) ℂ)
    (hP : P ∈ unitaryGroup (Fin N) ℂ) (hQ : Q ∈ unitaryGroup (Fin M) ℂ) :
    (SpikedWishart.SoftEdge.sampleLaw M N).map
        (fun X => fun m j => (P * (Matrix.of X)ᵀ * Q) j m) =
      SpikedWishart.SoftEdge.sampleLaw M N := by
  have hmeas : Measurable (fun X : Fin M → Fin N → ℂ => fun m j => (P * (Matrix.of X)ᵀ * Q) j m) := by
    apply Continuous.measurable
    simp only [mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have : IsProbabilityMeasure ((SpikedWishart.SoftEdge.sampleLaw M N).map
      (fun X => fun m j => (P * (Matrix.of X)ᵀ * Q) j m)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine ext_of_integral_char_eq Real.continuous_probChar Real.probChar_ne_one
    (L := Lpair M N) ?_ (continuous_Lpair M N) ?_
  · intro v hv h0
    apply hv
    have : Lpair M N v v = 0 := by rw [h0]; rfl
    rw [Lpair_apply] at this
    have := eq_zero_of_pair_self _ this
    funext m j
    exact congrFun (congrFun this m) j
  · intro w
    simp only [BoundedContinuousFunction.char_apply, Real.probChar_apply, Lpair_apply]
    rw [integral_map hmeas.aemeasurable (continuous_char_pair _).aestronglyMeasurable]
    have h3 : ∀ X : Fin M → Fin N → ℂ,
        pair (Matrix.of w) (Matrix.of (fun m j => (P * (Matrix.of X)ᵀ * Q) j m)) =
          pair (Q.map star * Matrix.of w * P.map star) (Matrix.of X) := by
      intro X
      rw [← pair_unitary]
      rfl
    simp_rw [h3]
    rw [sample_char, sample_char, pair_unitary_self _ _ _ hP hQ]

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

/-- Density of the standard exponential law. -/
noncomputable def dexp (w : ℝ) : ℝ := (Set.Ioi (0 : ℝ)).indicator (fun w => Real.exp (-w)) w

theorem dexp_nonneg (w : ℝ) : 0 ≤ dexp w := by
  unfold dexp; by_cases h : w ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]; exact (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem h]

theorem measurable_dexp : Measurable dexp :=
  (Real.continuous_exp.comp continuous_neg).measurable.indicator measurableSet_Ioi

/-- The standard exponential law `Exp(1)`. -/
noncomputable def exp1 : Measure ℝ := volume.withDensity (fun w => ENNReal.ofReal (dexp w))

theorem integrable_dexp : Integrable dexp := by
  unfold dexp
  rw [integrable_indicator_iff measurableSet_Ioi]
  have := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
  simpa using this

theorem integral_dexp : ∫ w, dexp w = 1 := by
  unfold dexp
  rw [integral_indicator measurableSet_Ioi, integral_exp_neg_Ioi_zero]

theorem isProb_exp1 : IsProbabilityMeasure exp1 := by
  constructor
  rw [exp1, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_dexp (Eventually.of_forall dexp_nonneg),
    integral_dexp, ENNReal.ofReal_one]

theorem integral_exp1 (g : ℝ → ℂ) : ∫ w, g w ∂exp1 = ∫ w in Set.Ioi 0, (Real.exp (-w) : ℂ) * g w := by
  have hm : Measurable (fun w => (dexp w).toNNReal) := measurable_dexp.real_toNNReal
  rw [exp1, show (fun w => ENNReal.ofReal (dexp w)) = (fun w => (((dexp w).toNNReal : NNReal) : ENNReal))
    from rfl, integral_withDensity_eq_integral_smul hm]
  unfold dexp
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext w
  by_cases h : w ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le,
      Complex.real_smul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp

theorem charFun_exp1 (t : ℝ) : charFun exp1 t = 1 / (1 - t * I) := by
  rw [charFun_apply_real, integral_exp1]
  have h : ∀ w : ℝ, (Real.exp (-w) : ℂ) * cexp (t * w * I) = cexp ((t * I - 1) * w) := by
    intro w; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [h]
  have hre : (t * I - 1 : ℂ).re < 0 := by simp
  rw [integral_exp_mul_complex_Ioi hre 0]
  have hne : (t * I - 1 : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this
  have hne2 : (1 - t * I : ℂ) ≠ 0 := by
    intro h0; apply hne; linear_combination -h0
  field_simp
  simp

theorem isProb_cg : IsProbabilityMeasure SpikedWishart.SoftEdge.stdComplexGaussian := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian
  exact Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

/-- `|g|²` of a standard complex Gaussian is `Exp(1)`. -/
theorem map_normSq_cg : SpikedWishart.SoftEdge.stdComplexGaussian.map Complex.normSq = exp1 := by
  have := isProb_cg
  have := isProb_exp1
  have : IsProbabilityMeasure (SpikedWishart.SoftEdge.stdComplexGaussian.map Complex.normSq) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_exp1, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  have := cg_normSq_char t
  convert this using 3
  push_cast; ring_nf

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

end Q2

end

-- ===== from Q2b.lean =====
section

namespace Q2

/-- Moments of the standard complex Gaussian: `E|z|^{2k} = k!`. -/
theorem integral_normSq_pow (k : ℕ) :
    ∫ z, Complex.normSq z ^ k ∂SpikedWishart.SoftEdge.stdComplexGaussian = (k.factorial : ℝ) := by
  have h1 : ∫ z, Complex.normSq z ^ k ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      ∫ w, w ^ k ∂Weyl.exp1 := by
    rw [← Weyl.map_normSq_cg, integral_map Complex.continuous_normSq.measurable.aemeasurable
      (continuous_pow k).aestronglyMeasurable]
  rw [h1]
  have hm : Measurable (fun w => (Weyl.dexp w).toNNReal) := Weyl.measurable_dexp.real_toNNReal
  rw [Weyl.exp1, show (fun w => ENNReal.ofReal (Weyl.dexp w)) =
    (fun w => (((Weyl.dexp w).toNNReal : NNReal) : ENNReal)) from rfl,
    integral_withDensity_eq_integral_smul hm]
  have h2 : (fun w => (Weyl.dexp w).toNNReal • w ^ k) =
      (Set.Ioi (0 : ℝ)).indicator (fun w => Real.exp (-w) * w ^ k) := by
    funext w
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Weyl.dexp_nonneg w)]
    unfold Weyl.dexp
    by_cases h : w ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [h2, integral_indicator measurableSet_Ioi]
  have h3 := Real.Gamma_eq_integral (s := (k : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h3
  rw [h3]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
  rw [add_sub_cancel_right, Real.rpow_natCast]

theorem integrable_normSq_pow (k : ℕ) :
    Integrable (fun z => Complex.normSq z ^ k) SpikedWishart.SoftEdge.stdComplexGaussian := by
  apply Integrable.of_integral_ne_zero
  rw [integral_normSq_pow]
  exact_mod_cast Nat.factorial_ne_zero k

theorem integrable_X : Integrable (fun z => Complex.normSq z - 1) SpikedWishart.SoftEdge.stdComplexGaussian := by
  have h := integrable_normSq_pow 1
  simp only [pow_one] at h
  exact h.sub (integrable_const _)

theorem integral_X : ∫ z, (Complex.normSq z - 1) ∂SpikedWishart.SoftEdge.stdComplexGaussian = 0 := by
  have h := integrable_normSq_pow 1
  simp only [pow_one] at h
  rw [integral_sub h (integrable_const _)]
  have h1 := integral_normSq_pow 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h1
  rw [h1]
  simp

theorem integrable_X_sq :
    Integrable (fun z => (Complex.normSq z - 1) ^ 2) SpikedWishart.SoftEdge.stdComplexGaussian := by
  have e : (fun z => (Complex.normSq z - 1) ^ 2) =
      fun z => Complex.normSq z ^ 2 - 2 * Complex.normSq z ^ 1 + 1 := by
    funext z; ring
  rw [e]
  exact ((integrable_normSq_pow 2).sub ((integrable_normSq_pow 1).const_mul 2)).add (integrable_const _)

theorem integral_X_sq :
    ∫ z, (Complex.normSq z - 1) ^ 2 ∂SpikedWishart.SoftEdge.stdComplexGaussian = 1 := by
  have e : (fun z => (Complex.normSq z - 1) ^ 2) =
      fun z => Complex.normSq z ^ 2 - 2 * Complex.normSq z ^ 1 + 1 := by
    funext z; ring
  have hI : Integrable (fun z => Complex.normSq z ^ 2 - 2 * Complex.normSq z ^ 1)
      SpikedWishart.SoftEdge.stdComplexGaussian :=
    (integrable_normSq_pow 2).sub ((integrable_normSq_pow 1).const_mul 2)
  rw [e, integral_add hI (integrable_const _), integral_sub (integrable_normSq_pow 2) ((integrable_normSq_pow 1).const_mul 2),
    integral_const_mul, integral_normSq_pow, integral_normSq_pow]
  norm_num

/-- The i.i.d. complex Gaussian vector law. -/
noncomputable abbrev cgv (n : ℕ) : Measure (Fin n → ℂ) :=
  Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian

theorem cgv_unitary {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : P ∈ unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun b : Fin n → ℂ => P *ᵥ b) (cgv n) (cgv n) := by
  have := Weyl.isProb_cg
  have he : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) (Fin n → ℂ))
      (SpikedWishart.SoftEdge.sampleLaw 1 n) (cgv n) :=
    measurePreserving_funUnique _ _
  have hT : MeasurePreserving
      (fun X : Fin 1 → Fin n → ℂ => fun m j => (P * (Matrix.of X)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℂ)) j m)
      (SpikedWishart.SoftEdge.sampleLaw 1 n) (SpikedWishart.SoftEdge.sampleLaw 1 n) := by
    refine ⟨?_, sample_invariant 1 n P 1 hP (one_mem _)⟩
    apply Continuous.measurable
    simp only [mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have hc := he.comp (hT.comp he.symm)
  convert hc using 1
  funext b
  ext j
  simp [MeasurableEquiv.funUnique, mulVec, dotProduct, mul_apply]

theorem integral_unitary {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : P ∈ unitaryGroup (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (hg : Measurable g) :
    ∫ y, g (P *ᵥ y) ∂cgv n = ∫ y, g y ∂cgv n := by
  have h := cgv_unitary P hP
  conv_rhs => rw [← h.map_eq]
  rw [integral_map h.measurable.aemeasurable (by rw [h.map_eq]; exact hg.aestronglyMeasurable)]

theorem integral_coord {n : ℕ} (i : Fin n) (f : ℂ → ℝ) (hf : Measurable f) :
    ∫ y, f (y i) ∂cgv n = ∫ z, f z ∂SpikedWishart.SoftEdge.stdComplexGaussian := by
  have h := measurePreserving_eval (fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian) i
  conv_rhs => rw [← h.map_eq]
  rw [integral_map h.measurable.aemeasurable (by rw [h.map_eq]; exact hf.aestronglyMeasurable)]

theorem integrable_coord {n : ℕ} (i : Fin n) (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable f SpikedWishart.SoftEdge.stdComplexGaussian) :
    Integrable (fun y : Fin n → ℂ => f (y i)) (cgv n) := by
  have h := measurePreserving_eval (fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian) i
  rw [← h.map_eq] at hi
  exact (integrable_map_measure hf.aestronglyMeasurable h.measurable.aemeasurable).1 hi

theorem integrable_XX {n : ℕ} (i j : Fin n) :
    Integrable (fun w : Fin n → ℂ => (Complex.normSq (w i) - 1) * (Complex.normSq (w j) - 1)) (cgv n) := by
  have hm : Measurable (fun z : ℂ => Complex.normSq z - 1) :=
    Complex.continuous_normSq.measurable.sub_const 1
  by_cases hij : i = j
  · subst hij
    have := integrable_coord i (fun z => (Complex.normSq z - 1) ^ 2) (hm.pow_const 2) integrable_X_sq
    simpa [pow_two] using this
  · have hind := (iIndepFun_pi (μ := fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
      (X := fun _ : Fin n => fun z : ℂ => Complex.normSq z - 1) (fun _ => hm.aemeasurable)).indepFun hij
    exact hind.integrable_mul (integrable_coord i _ hm integrable_X) (integrable_coord j _ hm integrable_X)

theorem integral_XX {n : ℕ} (i j : Fin n) :
    ∫ w : Fin n → ℂ, (Complex.normSq (w i) - 1) * (Complex.normSq (w j) - 1) ∂cgv n =
      if i = j then 1 else 0 := by
  have hm : Measurable (fun z : ℂ => Complex.normSq z - 1) :=
    Complex.continuous_normSq.measurable.sub_const 1
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have := integral_coord i (fun z => (Complex.normSq z - 1) ^ 2) (hm.pow_const 2)
    simp only [pow_two] at this
    rw [this]
    have h2 := integral_X_sq
    simp only [pow_two] at h2
    exact h2
  · rw [if_neg hij]
    have hind := (iIndepFun_pi (μ := fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
      (X := fun _ : Fin n => fun z : ℂ => Complex.normSq z - 1) (fun _ => hm.aemeasurable)).indepFun hij
    rw [hind.integral_fun_mul_eq_mul_integral (hm.comp (measurable_pi_apply i)).aestronglyMeasurable
      (hm.comp (measurable_pi_apply j)).aestronglyMeasurable]
    have h1 : ∫ y : Fin n → ℂ, (Complex.normSq (y i) - 1) ∂cgv n = 0 := by
      rw [integral_coord i (fun z => Complex.normSq z - 1) hm]; exact integral_X
    simp only [h1, zero_mul]

/-- Real quadratic form `Re (yᴴ B y)`. -/
noncomputable def qform {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) : ℝ :=
  (star y ⬝ᵥ (B *ᵥ y)).re

theorem qform_eig {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) (y : Fin n → ℂ) :
    qform B y = ∑ i, hB.eigenvalues i *
      Complex.normSq ((star (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) i) := by
  have hd := herm_decomp hB
  unfold qform
  generalize hU : (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = U at hd ⊢
  generalize hD : diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) = D at hd
  have key : star y ⬝ᵥ (B *ᵥ y) = star (star U *ᵥ y) ⬝ᵥ (D *ᵥ (star U *ᵥ y)) := by
    rw [hd, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [key, ← hD]
  simp only [mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.star_def, ← mul_assoc, mul_comm ((starRingEnd ℂ) _), mul_assoc,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem sum_eig_eq_trace {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    ∑ i, hB.eigenvalues i = (trace B).re := by
  rw [hB.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp

theorem measurable_wsum {n : ℕ} (d : Fin n → ℝ) (c : ℝ) :
    Measurable (fun w : Fin n → ℂ => ∑ i, d i * (Complex.normSq (w i) - c)) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul
    ((Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)).sub_const c))

/-- `E[yᴴ B y] = tr B` for Hermitian `B`. -/
theorem integral_qform {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    ∫ y, qform B y ∂cgv n = (trace B).re := by
  set U := (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hU : star U ∈ unitaryGroup (Fin n) ℂ := Unitary.star_mem hB.eigenvectorUnitary.2
  have e1 : (fun y => qform B y) = fun y => (fun w : Fin n → ℂ =>
      ∑ i, hB.eigenvalues i * (Complex.normSq (w i) - 0)) (star U *ᵥ y) := by
    funext y; rw [qform_eig hB]; simp only [sub_zero]; rfl
  rw [e1, integral_unitary (star U) hU _ (measurable_wsum _ _)]
  rw [integral_finsetSum _ (fun i _ => (integrable_coord i (fun z => Complex.normSq z - 0) (Complex.continuous_normSq.measurable.sub_const 0)
    (by simpa using integrable_normSq_pow 1)).const_mul _)]
  rw [← sum_eig_eq_trace hB]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, integral_coord i (fun z => Complex.normSq z - 0) (Complex.continuous_normSq.measurable.sub_const 0)]
  have h1 := integral_normSq_pow 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h1
  simp [h1]

/-- `E[(yᴴ B y - tr B)²] = Σ λᵢ²` for Hermitian `B` (complex Gaussian `y`). -/
theorem integral_qform_sq {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    ∫ y, (qform B y - (trace B).re) ^ 2 ∂cgv n = ∑ i, hB.eigenvalues i ^ 2 := by
  set U := (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hU : star U ∈ unitaryGroup (Fin n) ℂ := Unitary.star_mem hB.eigenvectorUnitary.2
  have e1 : (fun y => (qform B y - (trace B).re) ^ 2) = fun y => (fun w : Fin n → ℂ =>
      (∑ i, hB.eigenvalues i * (Complex.normSq (w i) - 1)) ^ 2) (star U *ᵥ y) := by
    funext y
    rw [qform_eig hB, ← sum_eig_eq_trace hB]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rfl
  rw [e1, integral_unitary (star U) hU _ ((measurable_wsum _ _).pow_const 2)]
  have e2 : (fun w : Fin n → ℂ => (∑ i, hB.eigenvalues i * (Complex.normSq (w i) - 1)) ^ 2) =
      fun w => ∑ i, ∑ j, (hB.eigenvalues i * hB.eigenvalues j) *
        ((Complex.normSq (w i) - 1) * (Complex.normSq (w j) - 1)) := by
    funext w
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [e2, integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (integrable_XX i j).const_mul _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => (integrable_XX i j).const_mul _)]
  simp only [integral_const_mul, integral_XX, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  ring

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

theorem sq_sub_bound {a b C D : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ D) : |(a - b) ^ 2| ≤ (C + D) ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h : |a - b| ≤ C + D := (abs_sub _ _).trans (add_le_add ha hb)
  calc (a - b) ^ 2 = |a - b| ^ 2 := (sq_abs _).symm
    _ ≤ (C + D) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2

/-- `E(φ - c)² = Var φ + (Eφ - c)²` for bounded measurable `φ`. -/
theorem var_split {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (φ : α → ℝ)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ x, |φ x| ≤ C) (c : ℝ) :
    ∫ x, (φ x - c) ^ 2 ∂μ = ∫ x, (φ x - ∫ y, φ y ∂μ) ^ 2 ∂μ + (∫ y, φ y ∂μ - c) ^ 2 := by
  set m := ∫ y, φ y ∂μ with hm
  have hmC : |m| ≤ C := abs_int_le C hC
  have e : ∀ x, (φ x - c) ^ 2 = (φ x - m) ^ 2 + ((2 * (m - c)) * φ x + ((m - c) ^ 2 - 2 * (m - c) * m)) := by
    intro x; ring
  simp_rw [e]
  have i1 : Integrable (fun x => (φ x - m) ^ 2) μ :=
    iob (by fun_prop) ((C + C) ^ 2) (fun x => sq_sub_bound (hC x) hmC)
  have i2 : Integrable φ μ := iob hφ C hC
  have i3 : Integrable (fun x => 2 * (m - c) * φ x + ((m - c) ^ 2 - 2 * (m - c) * m)) μ :=
    (i2.const_mul _).add (integrable_const _)
  have i4 : Integrable (fun x => 2 * (m - c) * φ x) μ := i2.const_mul _
  rw [integral_add i1 i3, integral_add i4 (integrable_const _), integral_const_mul, integral_const, probReal_univ, ← hm]
  simp only [smul_eq_mul, one_mul]
  ring

theorem jensen_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (φ : α → ℝ)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ x, |φ x| ≤ C) :
    (∫ x, φ x ∂μ) ^ 2 ≤ ∫ x, φ x ^ 2 ∂μ := by
  have h := var_split μ φ hφ C hC 0
  simp only [sub_zero] at h
  rw [h]
  have : 0 ≤ ∫ x, (φ x - ∫ y, φ y ∂μ) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  linarith

theorem measurable_Ek {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] {n : ℕ}
    (f : (Fin n → E) → ℝ) (hf : Measurable f) (k : Fin n) :
    Measurable (fun x : Fin n → E => ∫ w, f (Function.update x k w) ∂ν) :=
  ((hf.comp (measurable_update' (a := k))).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

theorem snoc_symm {E : Type*} [MeasurableSpace E] {n : ℕ} (z : E) (r : Fin n → E) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).symm (z, r) =
      Fin.snoc (α := fun _ => E) r z := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_last']

/-- The Efron–Stein inequality for bounded measurable functions of i.i.d. coordinates. -/
theorem efron_stein {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] :
    ∀ (n : ℕ) (f : (Fin n → E) → ℝ) (C : ℝ), Measurable f → (∀ x, |f x| ≤ C) →
    ∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => ν)) ^ 2 ∂(Measure.pi fun _ : Fin n => ν) ≤
      ∑ k, ∫ x, (f x - ∫ w, f (Function.update x k w) ∂ν) ^ 2 ∂(Measure.pi fun _ : Fin n => ν)
  | 0, f, C, hf, hC => by
    have hc : ∀ y : Fin 0 → E, f y = f (fun i => i.elim0) := fun y => congrArg f (Subsingleton.elim _ _)
    simp [hc]
  | n + 1, f, C, hf, hC => by
    set π1 := Measure.pi fun _ : Fin (n + 1) => ν
    set π0 := Measure.pi fun _ : Fin n => ν
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n) with hedef
    have hmp : MeasurePreserving e π1 (ν.prod π0) :=
      measurePreserving_piFinSuccAbove (fun _ => ν) (Fin.last n)
    have tr : ∀ G : (Fin (n + 1) → E) → ℝ, ∫ x, G x ∂π1 = ∫ p, G (e.symm p) ∂(ν.prod π0) :=
      fun G => (hmp.symm.integral_comp' G).symm
    have fub : ∀ (G : E × (Fin n → E) → ℝ) (D : ℝ), Measurable G → (∀ p, |G p| ≤ D) →
        ∫ p, G p ∂(ν.prod π0) = ∫ r, ∫ z, G (z, r) ∂ν ∂π0 :=
      fun G D hG hD => integral_prod_symm G (iob hG D hD)
    set F : E × (Fin n → E) → ℝ := fun p => f (e.symm p) with hFdef
    have hF : Measurable F := hf.comp e.symm.measurable
    have hFC : ∀ p, |F p| ≤ C := fun p => hC _
    set h : (Fin n → E) → ℝ := fun r => ∫ z, F (z, r) ∂ν with hhdef
    have hh : Measurable h := (hF.stronglyMeasurable.integral_prod_left' (μ := ν)).measurable
    have hhC : ∀ r, |h r| ≤ C := fun r => abs_int_le C (fun z => hFC _)
    have hm : ∫ y, f y ∂π1 = ∫ r, h r ∂π0 := by rw [tr f, fub F C hF hFC]
    set m := ∫ r, h r ∂π0 with hmdef
    have hmC : |m| ≤ C := abs_int_le C hhC
    -- the law of total variance
    have hL : ∫ x, (f x - ∫ y, f y ∂π1) ^ 2 ∂π1 =
        ∫ r, ∫ z, (F (z, r) - h r) ^ 2 ∂ν ∂π0 + ∫ r, (h r - m) ^ 2 ∂π0 := by
      rw [hm, tr, fub (fun p => (F p - m) ^ 2) ((C + C) ^ 2) (by fun_prop)
        (fun p => sq_sub_bound (hFC p) hmC)]
      have hG : Measurable (fun p : E × (Fin n → E) => (F p - h p.2) ^ 2) :=
        (hF.sub (hh.comp measurable_snd)).pow_const 2
      rw [← integral_add (iob (hG.stronglyMeasurable.integral_prod_left' (μ := ν)).measurable ((C + C) ^ 2)
        (fun r => abs_int_le _ (fun z => sq_sub_bound (hFC _) (hhC r))))
        (iob (by fun_prop) ((C + C) ^ 2) (fun r => sq_sub_bound (hhC r) hmC))]
      refine integral_congr_ae (ae_of_all _ (fun r => ?_))
      exact var_split ν (fun z => F (z, r)) (hF.comp (measurable_id.prodMk measurable_const)) C
        (fun z => hFC _) m
    -- the last coordinate
    have hA : ∫ r, ∫ z, (F (z, r) - h r) ^ 2 ∂ν ∂π0 =
        ∫ x, (f x - ∫ w, f (Function.update x (Fin.last n) w) ∂ν) ^ 2 ∂π1 := by
      have hE := measurable_Ek ν f hf (Fin.last n)
      have hGm : Measurable (fun p => (f (e.symm p) -
          ∫ w, f (Function.update (e.symm p) (Fin.last n) w) ∂ν) ^ 2) :=
        (hF.sub (hE.comp e.symm.measurable)).pow_const 2
      rw [tr, fub _ ((C + C) ^ 2) hGm (fun p => sq_sub_bound (hFC p) (abs_int_le C (fun w => hC _)))]
      refine integral_congr_ae (ae_of_all _ (fun r => integral_congr_ae (ae_of_all _ (fun z => ?_))))
      simp only [hFdef, hhdef, hedef, snoc_symm, Fin.update_snoc_last]
    -- the other coordinates
    have hB : ∀ j : Fin n, ∫ r, (h r - ∫ w, h (Function.update r j w) ∂ν) ^ 2 ∂π0 ≤
        ∫ x, (f x - ∫ w, f (Function.update x j.castSucc w) ∂ν) ^ 2 ∂π1 := by
      intro j
      have hE := measurable_Ek ν f hf j.castSucc
      have hGm : Measurable (fun p => (f (e.symm p) -
          ∫ w, f (Function.update (e.symm p) j.castSucc w) ∂ν) ^ 2) :=
        (hF.sub (hE.comp e.symm.measurable)).pow_const 2
      have hEh := measurable_Ek ν h hh j
      have hK : Measurable (fun q : (E × (Fin n → E)) × E => F (q.1.1, Function.update q.1.2 j q.2)) :=
        hF.comp (measurable_fst.fst.prodMk ((measurable_update' (a := j)).comp
          (measurable_fst.snd.prodMk measurable_snd)))
      have hK2 : Measurable (fun p : E × (Fin n → E) => ∫ w, F (p.1, Function.update p.2 j w) ∂ν) :=
        (hK.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
      have hR : ∫ x, (f x - ∫ w, f (Function.update x j.castSucc w) ∂ν) ^ 2 ∂π1 =
          ∫ r, ∫ z, (F (z, r) - ∫ w, F (z, Function.update r j w) ∂ν) ^ 2 ∂ν ∂π0 := by
        rw [tr, fub _ ((C + C) ^ 2) hGm (fun p => sq_sub_bound (hFC p) (abs_int_le C (fun w => hC _)))]
        refine integral_congr_ae (ae_of_all _ (fun r => integral_congr_ae (ae_of_all _ (fun z => ?_))))
        simp only [hFdef, hedef, snoc_symm, Fin.snoc_update]
      rw [hR]
      refine integral_mono (iob ((hh.sub hEh).pow_const 2) ((C + C) ^ 2)
          (fun r => sq_sub_bound (hhC r) (abs_int_le C (fun w => hhC _))))
        (iob (((hF.sub hK2).pow_const 2).stronglyMeasurable.integral_prod_left' (μ := ν)).measurable
          ((C + C) ^ 2) (fun r => abs_int_le _ (fun z => sq_sub_bound (hFC _)
            (abs_int_le C (fun w => hFC _))))) (fun r => ?_)
      have hsw : ∫ w, h (Function.update r j w) ∂ν = ∫ z, ∫ w, F (z, Function.update r j w) ∂ν ∂ν := by
        simp only [hhdef]
        refine integral_integral_swap (f := fun w z => F (z, Function.update r j w)) ?_
        refine iob ?_ C (fun q => hFC _)
        exact hF.comp (measurable_snd.prodMk ((measurable_update' (a := j)).comp
          (measurable_const.prodMk measurable_fst)))
      have e1 : h r - ∫ w, h (Function.update r j w) ∂ν =
          ∫ z, (F (z, r) - ∫ w, F (z, Function.update r j w) ∂ν) ∂ν := by
        have i5 : Integrable (fun z => F (z, r)) ν :=
          iob (hF.comp (measurable_id.prodMk measurable_const)) C (fun z => hFC _)
        have i6 : Integrable (fun z => ∫ w, F (z, Function.update r j w) ∂ν) ν :=
          iob (hK2.comp (measurable_id.prodMk measurable_const)) C (fun z => abs_int_le C (fun w => hFC _))
        rw [hsw, integral_sub i5 i6]
      simp only
      rw [e1]
      refine (jensen_sq ν _ ((hF.sub hK2).comp (measurable_id.prodMk measurable_const)) (C + C)
        (fun z => (abs_sub _ _).trans (add_le_add (hFC _) (abs_int_le C (fun w => hFC _))))).trans (le_of_eq ?_)
      rfl
    have IH := efron_stein ν n h C hh hhC
    rw [← hmdef] at IH
    rw [hL, Fin.sum_univ_castSucc, ← hA]
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hB j)
    linarith

end Q2

end

-- ===== from Q2d.lean =====
section

namespace Q2

theorem vmv_mulVec {p : ℕ} (u v w : Fin p → ℂ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Sherman–Morrison on a vector: `(1 - q) (A - vvᴴ)⁻¹ v = A⁻¹ v`, `q = vᴴ A⁻¹ v`. -/
theorem sm_vec {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A.det) (v : Fin p → ℂ)
    (hB : IsUnit (A - vecMulVec v (star v)).det) :
    (1 - star v ⬝ᵥ (A⁻¹ *ᵥ v)) • ((A - vecMulVec v (star v))⁻¹ *ᵥ v) = A⁻¹ *ᵥ v := by
  set B := A - vecMulVec v (star v)
  have h1 : B *ᵥ (A⁻¹ *ᵥ v) = (1 - star v ⬝ᵥ (A⁻¹ *ᵥ v)) • v := by
    simp only [B]
    rw [sub_mulVec, mulVec_mulVec _ A A⁻¹, mul_nonsing_inv _ hA, one_mulVec, vmv_mulVec, sub_smul, one_smul]
  have h2 : B⁻¹ *ᵥ (B *ᵥ (A⁻¹ *ᵥ v)) = A⁻¹ *ᵥ v := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hB, one_mulVec]
  calc (1 - star v ⬝ᵥ (A⁻¹ *ᵥ v)) • (B⁻¹ *ᵥ v) = B⁻¹ *ᵥ ((1 - star v ⬝ᵥ (A⁻¹ *ᵥ v)) • v) :=
        (mulVec_smul _ _ _).symm
    _ = B⁻¹ *ᵥ (B *ᵥ (A⁻¹ *ᵥ v)) := by rw [h1]
    _ = A⁻¹ *ᵥ v := h2

/-- Resolvent identity for a rank-one update: `tr B⁻¹ - tr A⁻¹ = vᴴ A⁻¹ B⁻¹ v`. -/
theorem sm_trace {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A.det) (v : Fin p → ℂ)
    (hB : IsUnit (A - vecMulVec v (star v)).det) :
    trace (A - vecMulVec v (star v))⁻¹ - trace A⁻¹ =
      star v ⬝ᵥ (A⁻¹ *ᵥ ((A - vecMulVec v (star v))⁻¹ *ᵥ v)) := by
  set B := A - vecMulVec v (star v)
  have e : B⁻¹ - A⁻¹ = B⁻¹ * vecMulVec v (star v) * A⁻¹ := by
    have : vecMulVec v (star v) = A - B := by simp [B]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, nonsing_inv_mul _ hB, Matrix.mul_assoc, mul_nonsing_inv _ hA,
      Matrix.one_mul, Matrix.mul_one]
  rw [← trace_sub, e, mul_vecMulVec, vecMulVec_mul, trace_vecMulVec, dotProduct_comm, ← dotProduct_mulVec]

/-- `tr B⁻¹ - tr A⁻¹ = u / (1 - q)` with `u = vᴴ A⁻² v`. -/
theorem sm_trace' {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A.det) (v : Fin p → ℂ)
    (hB : IsUnit (A - vecMulVec v (star v)).det) :
    (1 - star v ⬝ᵥ (A⁻¹ *ᵥ v)) * (trace (A - vecMulVec v (star v))⁻¹ - trace A⁻¹) =
      star v ⬝ᵥ ((A⁻¹ * A⁻¹) *ᵥ v) := by
  rw [sm_trace A hA v hB]
  have h := sm_vec A hA v hB
  calc (1 - star v ⬝ᵥ (A⁻¹ *ᵥ v)) * (star v ⬝ᵥ (A⁻¹ *ᵥ ((A - vecMulVec v (star v))⁻¹ *ᵥ v))) =
        star v ⬝ᵥ (A⁻¹ *ᵥ ((1 - star v ⬝ᵥ (A⁻¹ *ᵥ v)) • ((A - vecMulVec v (star v))⁻¹ *ᵥ v))) := by
        rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
    _ = star v ⬝ᵥ ((A⁻¹ * A⁻¹) *ᵥ v) := by rw [h, mulVec_mulVec]

/-- Quadratic form in an eigenbasis. -/
theorem quad_conj {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (d : Fin p → ℂ) (v : Fin p → ℂ) :
    star v ⬝ᵥ ((U * diagonal d * star U) *ᵥ v) =
      ∑ i, star ((star U *ᵥ v) i) * (d i * (star U *ᵥ v) i) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    show star v ᵥ* U = star (star U *ᵥ v) by
      rw [star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]]
  simp only [mulVec_diagonal, dotProduct, Pi.star_apply]

theorem star_mulVec_dot {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (b v : Fin p → ℂ) :
    star (U *ᵥ b) ⬝ᵥ v = star b ⬝ᵥ (star U *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec, Matrix.star_eq_conjTranspose]

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

theorem smul_sub_eig {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) (x : ℝ) :
    (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K =
      (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) *
        diagonal (fun i => (((x - hK.eigenvalues i : ℝ)) : ℂ)) *
        star (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) := by
  set U := (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) with hUdef
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hK.eigenvectorUnitary
  have hd : K = U * diagonal (fun i => ((hK.eigenvalues i : ℝ) : ℂ)) * star U := herm_decomp hK
  have h1 : (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) = U * diagonal (fun _ => (x : ℂ)) * star U := by
    rw [show diagonal (fun _ => (x : ℂ)) = (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) by
      ext i j; simp [diagonal_apply, one_apply], Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU']
  have h2 : (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K =
      (x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - U * diagonal (fun i => ((hK.eigenvalues i : ℝ) : ℂ)) * star U := by
    rw [← hd]
  rw [h2, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  congr 3
  funext i
  push_cast
  ring

theorem conj_term (c : ℂ) (τ : ℝ) (hτ : τ ≠ 0) :
    star (c / (τ : ℂ)) * ((τ : ℂ) * (c / (τ : ℂ))) = ((Complex.normSq c / τ : ℝ) : ℂ) := by
  have hτ' : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [Complex.star_def, map_div₀, Complex.conj_ofReal, Complex.ofReal_div, Complex.normSq_eq_conj_mul_self]
  field_simp

theorem conj_term' (c : ℂ) (τ : ℝ) :
    star c * ((τ : ℂ) * c) = ((τ * Complex.normSq c : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  ring

/-- Key a-priori bound: if `t - (K + vvᴴ) ⪰ 0`, `0 ≤ K`, `eig K < t < x`, then `vᴴ (x - K)⁻¹ v ≤ t / x`. -/
theorem q_le {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) (hK0 : ∀ i, 0 ≤ hK.eigenvalues i)
    (v : Fin p → ℂ) (t x : ℝ) (ht : 0 < t) (htx : t < x) (hμt : ∀ i, hK.eigenvalues i < t)
    (hpsd : ∀ w : Fin p → ℂ, Complex.normSq (star w ⬝ᵥ v) ≤
      (star w ⬝ᵥ (((t : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K) *ᵥ w)).re) :
    (star v ⬝ᵥ (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ *ᵥ v)).re ≤ t / x := by
  set U := (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) with hUdef
  set μ := hK.eigenvalues with hμdef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hK.eigenvectorUnitary
  set c : Fin p → ℂ := star U *ᵥ v with hc
  set b : Fin p → ℂ := fun i => c i / ((t - μ i : ℝ) : ℂ) with hb
  have htμ : ∀ i, (t - μ i : ℝ) ≠ 0 := fun i => (sub_pos.mpr (hμt i)).ne'
  have hUb : star U *ᵥ (U *ᵥ b) = b := by rw [mulVec_mulVec, hUU, one_mulVec]
  set s : ℝ := ∑ i, Complex.normSq (c i) / (t - μ i) with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ =>
    div_nonneg (Complex.normSq_nonneg _) (sub_pos.mpr (hμt i)).le)
  have hquad : (star (U *ᵥ b) ⬝ᵥ (((t : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K) *ᵥ (U *ᵥ b))).re = s := by
    rw [smul_sub_eig hK t, quad_conj, hUb]
    simp only [hb]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [conj_term _ _ (htμ i), Complex.ofReal_re]
  have hdot : star (U *ᵥ b) ⬝ᵥ v = (s : ℂ) := by
    rw [star_mulVec_dot, ← hc]
    simp only [dotProduct, Pi.star_apply, hb, hs, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hτ' : ((t - μ i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (htμ i)
    rw [Complex.star_def, map_div₀, Complex.conj_ofReal, Complex.ofReal_div, Complex.normSq_eq_conj_mul_self]
    field_simp
  have h1 := hpsd (U *ᵥ b)
  rw [hquad, hdot, Complex.normSq_ofReal] at h1
  have hs1 : s ≤ 1 := by nlinarith
  have hxμ : ∀ i, (x - μ i : ℝ) ≠ 0 := fun i => (sub_pos.mpr ((hμt i).trans htx)).ne'
  rw [inv_eig hK x (fun i h => hxμ i (by show x - hK.eigenvalues i = 0; rw [h, sub_self])), quad_conj, Complex.re_sum]
  have hterm : ∀ i, (star ((star U *ᵥ v) i) * ((((x - μ i)⁻¹ : ℝ) : ℂ) * (star U *ᵥ v) i)).re ≤
      t / x * (Complex.normSq (c i) / (t - μ i)) := by
    intro i
    rw [conj_term', Complex.ofReal_re]
    have hn := Complex.normSq_nonneg (c i)
    have hμ0 := hK0 i
    have h1' : 0 < t - μ i := sub_pos.mpr (hμt i)
    have h2' : 0 < x - μ i := sub_pos.mpr ((hμt i).trans htx)
    have hx0 : 0 < x := ht.trans htx
    have key : (x - μ i)⁻¹ ≤ t / x / (t - μ i) := by
      rw [inv_eq_one_div, div_div, div_le_div_iff₀ h2' (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right htx.le hμ0]
    calc (x - μ i)⁻¹ * Complex.normSq (c i) ≤ t / x / (t - μ i) * Complex.normSq (c i) :=
          mul_le_mul_of_nonneg_right key hn
      _ = t / x * (Complex.normSq (c i) / (t - μ i)) := by ring
  calc ∑ i, (star ((star U *ᵥ v) i) * ((((x - μ i)⁻¹ : ℝ) : ℂ) * (star U *ᵥ v) i)).re
      ≤ ∑ i, t / x * (Complex.normSq (c i) / (t - μ i)) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = t / x * s := by rw [← Finset.mul_sum]
    _ ≤ t / x * 1 := mul_le_mul_of_nonneg_left hs1 (div_nonneg ht.le (ht.trans htx).le)
    _ = t / x := mul_one _

/-- PSD of `t - (K + vvᴴ)` in the form used by `q_le`. -/
theorem hpsd_of_psd {p : ℕ} (K : Matrix (Fin p) (Fin p) ℂ) (v : Fin p → ℂ) (t : ℝ)
    (h : ((t : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (K + vecMulVec v (star v))).PosSemidef) :
    ∀ w : Fin p → ℂ, Complex.normSq (star w ⬝ᵥ v) ≤
      (star w ⬝ᵥ (((t : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K) *ᵥ w)).re := by
  intro w
  have h2 := ((posSemidef_iff_dotProduct_mulVec.mp h).2 w)
  have h3 := (Complex.le_def.mp h2).1
  rw [sub_add_eq_sub_sub, sub_mulVec, vmv_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    Complex.sub_re] at h3
  have e : (star w ⬝ᵥ v * (star v ⬝ᵥ w)).re = Complex.normSq (star w ⬝ᵥ v) := by
    have : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by
      rw [← star_dotProduct_star, star_star]
    rw [this, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  rw [mul_comm] at e
  simp only [Complex.zero_re] at h3
  linarith

/-- `Σ λᵢ² = Re tr(B²)` for Hermitian `B`. -/
theorem sum_eig_sq_eq {p : ℕ} {B : Matrix (Fin p) (Fin p) ℂ} (hB : B.IsHermitian) :
    ∑ i, hB.eigenvalues i ^ 2 = (trace (B * B)).re := by
  have hd := herm_decomp hB
  set U := (hB.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have e : B * B = U * (diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) *
      diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ))) * star U := by
    conv_lhs => rw [hd]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
  rw [e, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.ofReal_mul, Complex.ofReal_re, pow_two]

/-- Trace of a matrix in conjugated diagonal form. -/
theorem trace_conj_diag {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : star U * U = 1) (d : Fin p → ℂ) :
    trace (U * diagonal d * star U) = ∑ i, d i := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, trace_diagonal]

end Q2

end

-- ===== from Q2e.lean =====
section

namespace Q2

/-- Resampling coordinate `k` of a product measure does not change integrals. -/
theorem resample {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] {n : ℕ}
    (G : (Fin n → E) → ℝ) (D : ℝ) (hG : Measurable G) (hD : ∀ x, |G x| ≤ D) (k : Fin n) :
    ∫ x, G x ∂(Measure.pi fun _ : Fin n => ν) =
      ∫ x, ∫ w, G (Function.update x k w) ∂ν ∂(Measure.pi fun _ : Fin n => ν) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.pos; omega⟩
  set π1 := Measure.pi fun _ : Fin (m + 1) => ν
  set π0 := Measure.pi fun _ : Fin m => ν
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E) k with hedef
  have hmp : MeasurePreserving e π1 (ν.prod π0) :=
    measurePreserving_piFinSuccAbove (fun _ => ν) k
  have tr : ∀ H : (Fin (m + 1) → E) → ℝ, ∫ x, H x ∂π1 = ∫ p, H (e.symm p) ∂(ν.prod π0) :=
    fun H => (hmp.symm.integral_comp' H).symm
  have fub : ∀ (H : E × (Fin m → E) → ℝ) (D' : ℝ), Measurable H → (∀ p, |H p| ≤ D') →
      ∫ p, H p ∂(ν.prod π0) = ∫ r, ∫ z, H (z, r) ∂ν ∂π0 :=
    fun H D' hH hD' => integral_prod_symm H (iob hH D' hD')
  have hes : ∀ (z : E) (r : Fin m → E), e.symm (z, r) = Fin.insertNth k z r := by
    intro z r
    simp [hedef, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hK : Measurable (fun x : Fin (m + 1) → E => ∫ w, G (Function.update x k w) ∂ν) :=
    measurable_Ek ν G hG k
  rw [tr G, fub (fun p => G (e.symm p)) D (hG.comp e.symm.measurable) (fun p => hD _), tr,
    fub (fun p => ∫ w, G (Function.update (e.symm p) k w) ∂ν) D (hK.comp e.symm.measurable)
      (fun p => abs_int_le D (fun w => hD _))]
  refine integral_congr_ae (ae_of_all _ (fun r => ?_))
  simp only [hes, Fin.update_insertNth]
  rw [integral_const, probReal_univ, one_smul]

/-- Efron-Stein proxy: the conditional variance in coordinate `k` is at most the mean square
distance to any function not depending on coordinate `k`. -/
theorem es_proxy {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] {n : ℕ}
    (f Φ : (Fin n → E) → ℝ) (C D : ℝ) (hf : Measurable f) (hfC : ∀ x, |f x| ≤ C)
    (hΦ : Measurable Φ) (hΦD : ∀ x, |Φ x| ≤ D) (k : Fin n)
    (hinv : ∀ x w, Φ (Function.update x k w) = Φ x) :
    ∫ x, (f x - ∫ w, f (Function.update x k w) ∂ν) ^ 2 ∂(Measure.pi fun _ : Fin n => ν) ≤
      ∫ x, (f x - Φ x) ^ 2 ∂(Measure.pi fun _ : Fin n => ν) := by
  have hE := measurable_Ek ν f hf k
  have hEC : ∀ x, |∫ w, f (Function.update x k w) ∂ν| ≤ C := fun x => abs_int_le C (fun w => hfC _)
  rw [resample ν (fun x => (f x - ∫ w, f (Function.update x k w) ∂ν) ^ 2) ((C + C) ^ 2)
      ((hf.sub hE).pow_const 2) (fun x => sq_sub_bound (hfC x) (hEC x)) k,
    resample ν (fun x => (f x - Φ x) ^ 2) ((C + D) ^ 2) ((hf.sub hΦ).pow_const 2)
      (fun x => sq_sub_bound (hfC x) (hΦD x)) k]
  have hm1 : Measurable (fun x => ∫ w, (f (Function.update x k w) -
      ∫ w', f (Function.update (Function.update x k w) k w') ∂ν) ^ 2 ∂ν) :=
    measurable_Ek ν _ ((hf.sub hE).pow_const 2) k
  have hm2 : Measurable (fun x => ∫ w, (f (Function.update x k w) - Φ (Function.update x k w)) ^ 2 ∂ν) :=
    measurable_Ek ν _ ((hf.sub hΦ).pow_const 2) k
  refine integral_mono (iob hm1 ((C + C) ^ 2) (fun x => abs_int_le _ (fun w => sq_sub_bound (hfC _) (hEC _))))
    (iob hm2 ((C + D) ^ 2) (fun x => abs_int_le _ (fun w => sq_sub_bound (hfC _) (hΦD _)))) (fun x => ?_)
  simp only [Function.update_idem, hinv]
  have hφ : Measurable (fun w => f (Function.update x k w)) := hf.comp (measurable_update x)
  rw [var_split ν (fun w => f (Function.update x k w)) hφ C (fun w => hfC _) (Φ x)]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The sample covariance `M⁻¹ Y Yᴴ`, `Y = (of X)ᵀ`, with columns `X k`. -/
noncomputable def Smat {M p : ℕ} (X : Fin M → Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ)

theorem Smat_apply {M p : ℕ} (X : Fin M → Fin p → ℂ) (i j : Fin p) :
    Smat X i j = (M : ℂ)⁻¹ * ∑ k, X k i * star (X k j) := by
  simp [Smat, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Replacing column `k`: `S(update X k w) = S(update X k 0) + M⁻¹ w wᴴ`. -/
theorem Smat_update {M p : ℕ} (X : Fin M → Fin p → ℂ) (k : Fin M) (w : Fin p → ℂ) :
    Smat (Function.update X k w) = Smat (Function.update X k 0) +
      (M : ℂ)⁻¹ • vecMulVec w (star w) := by
  ext i j
  rw [Matrix.add_apply, Smat_apply, Smat_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, ← mul_add]
  congr 1
  have h1 : ∑ l, Function.update X k w l i * star (Function.update X k w l j) =
      ∑ l, Function.update X k 0 l i * star (Function.update X k 0 l j) +
        (w i * star (w j)) := by
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Function.update_of_ne hl]
    · simp
  rw [h1]
  simp [Pi.star_apply]

open scoped ComplexOrder

/-- `Re tr (x - K)⁻¹`. -/
noncomputable def resT {p : ℕ} (x : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) : ℝ :=
  (trace (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹)).re

/-- `Re tr (x - K)⁻²`. -/
noncomputable def resT2 {p : ℕ} (x : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) : ℝ :=
  (trace (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ *
    ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹)).re

theorem psd_of_re {p : ℕ} {A : Matrix (Fin p) (Fin p) ℂ} (hA : A.IsHermitian)
    (h : ∀ z : Fin p → ℂ, 0 ≤ (star z ⬝ᵥ (A *ᵥ z)).re) : A.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨hA, fun z => Complex.nonneg_iff.mpr ⟨h z, ?_⟩⟩
  have := hA.im_star_dotProduct_mulVec_self z
  simp only [RCLike.im_to_complex] at this
  exact this.symm

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

theorem r_bound {u ub q qb κ U : ℝ} (hκ : 0 < κ) (hq : q ≤ 1 - κ) (hub0 : 0 ≤ ub) (hubU : ub ≤ U) :
    (u / (1 - q) - ub / (1 - min qb (1 - κ / 2))) ^ 2 ≤
      2 / κ ^ 2 * (u - ub) ^ 2 + 8 * U ^ 2 / κ ^ 4 * (q - qb) ^ 2 := by
  set qt := min qb (1 - κ / 2) with hqt
  have hA : κ ≤ 1 - q := by linarith
  have hB : κ / 2 ≤ 1 - qt := by have := min_le_right qb (1 - κ / 2); linarith
  have hA0 : 0 < 1 - q := by linarith
  have hB0 : 0 < 1 - qt := by linarith
  have hU0 : 0 ≤ U := le_trans hub0 hubU
  have hqq : |q - qt| ≤ |q - qb| := by
    rcases le_total qb (1 - κ / 2) with h | h
    · rw [hqt, min_eq_left h]
    · rw [hqt, min_eq_right h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  have e : u / (1 - q) - ub / (1 - qt) = (u - ub) / (1 - q) + ub * (q - qt) / ((1 - q) * (1 - qt)) := by
    field_simp
    ring
  rw [e]
  set a := (u - ub) / (1 - q) with ha_def
  set b := ub * (q - qt) / ((1 - q) * (1 - qt)) with hb_def
  have ha : |a| ≤ |u - ub| / κ := by
    rw [ha_def, abs_div, abs_of_pos hA0]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hκ hA
  have hb : |b| ≤ 2 * U / κ ^ 2 * |q - qb| := by
    rw [hb_def, abs_div, abs_mul, abs_of_nonneg hub0, abs_of_pos (mul_pos hA0 hB0),
      div_le_iff₀ (mul_pos hA0 hB0)]
    have h1 : κ * (κ / 2) ≤ (1 - q) * (1 - qt) := mul_le_mul hA hB (by linarith) hA0.le
    have h2 : 0 ≤ 2 * U / κ ^ 2 * |q - qb| := mul_nonneg (div_nonneg (by linarith) (by positivity)) (abs_nonneg _)
    calc ub * |q - qt| ≤ U * |q - qb| := mul_le_mul hubU hqq (abs_nonneg _) hU0
      _ = 2 * U / κ ^ 2 * |q - qb| * (κ * (κ / 2)) := by field_simp
      _ ≤ 2 * U / κ ^ 2 * |q - qb| * ((1 - q) * (1 - qt)) := mul_le_mul_of_nonneg_left h1 h2
  have hsq : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have ha2 : a ^ 2 ≤ (|u - ub| / κ) ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hb2 : b ^ 2 ≤ (2 * U / κ ^ 2 * |q - qb|) ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have e2 : (|u - ub| / κ) ^ 2 = (u - ub) ^ 2 / κ ^ 2 := by rw [div_pow, sq_abs]
  have e3 : (2 * U / κ ^ 2 * |q - qb|) ^ 2 = 4 * U ^ 2 / κ ^ 4 * (q - qb) ^ 2 := by
    rw [mul_pow, sq_abs]; ring
  rw [e2] at ha2
  rw [e3] at hb2
  have e4 : 2 / κ ^ 2 * (u - ub) ^ 2 = 2 * ((u - ub) ^ 2 / κ ^ 2) := by ring
  have e5 : 8 * U ^ 2 / κ ^ 4 * (q - qb) ^ 2 = 2 * (4 * U ^ 2 / κ ^ 4 * (q - qb) ^ 2) := by ring
  rw [e4, e5]
  linarith

theorem vmv_smul {p M : ℕ} (hM : 0 < M) (w : Fin p → ℂ) :
    vecMulVec ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) • w) (star ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) • w)) =
      (M : ℂ)⁻¹ • vecMulVec w (star w) := by
  have hr : ((((Real.sqrt M)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt M)⁻¹ : ℝ) : ℂ) = (M : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg M)]
    push_cast
    rfl
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_smul, smul_eq_mul, Complex.star_def,
    Complex.conj_ofReal, Matrix.smul_apply]
  rw [← hr]
  ring

theorem quad_smul {p : ℕ} (B : Matrix (Fin p) (Fin p) ℂ) (r : ℝ) (w : Fin p → ℂ) :
    (star ((r : ℂ) • w) ⬝ᵥ (B *ᵥ ((r : ℂ) • w))).re = r * r * qform B w := by
  rw [mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal, qform]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

theorem vmv_herm {p : ℕ} (v : Fin p → ℂ) : (vecMulVec v (star v)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, vecMulVec_apply, mul_comm]

/-- One rank-one step on the good event. -/
theorem good_step {p M : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x)
    {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) (hK0 : ∀ i, 0 ≤ hK.eigenvalues i) (w : Fin p → ℂ)
    (hgood : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
      (K + (M : ℂ)⁻¹ • vecMulVec w (star w))).PosSemidef) :
    (∀ i, hK.eigenvalues i ≤ e1) ∧
    (M : ℝ)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w ≤ 1 - (x - e1) / (2 * x) ∧
    resT x (K + (M : ℂ)⁻¹ • vecMulVec w (star w)) - resT x K =
      (M : ℝ)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ *
          ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w /
        (1 - (M : ℝ)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w) := by
  have hx0 : 0 < x := by linarith
  set r : ℝ := (Real.sqrt M)⁻¹ with hr
  set v : Fin p → ℂ := (r : ℂ) • w with hv
  have hrr : r * r = (M : ℝ)⁻¹ := by
    rw [hr, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg M)]
  have hvv : vecMulVec v (star v) = (M : ℂ)⁻¹ • vecMulVec w (star w) := vmv_smul hM w
  rw [← hvv] at hgood ⊢
  have hS : (K + vecMulVec v (star v)).IsHermitian := hK.add (vmv_herm v)
  have hKe : ∀ i, hK.eigenvalues i ≤ e1 :=
    (eig_le_iff_posSemidef hK e1).mpr (psd_of_re (isHermitian_smul_one_sub hK e1)
      (fun z => le_trans (Complex.normSq_nonneg _) (hpsd_of_psd K v e1 hgood z)))
  have hSe : ∀ j, hS.eigenvalues j ≤ e1 := (eig_le_iff_posSemidef hS e1).mpr hgood
  have hA : IsUnit ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K).det :=
    unit_of_eig hK (fun i => by linarith [hKe i])
  have hB : IsUnit (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K) - vecMulVec v (star v)).det := by
    rw [sub_sub]; exact unit_of_eig hS (fun j => by linarith [hSe j])
  set t := (x + e1) / 2 with ht
  have hq := q_le hK hK0 v t x (by linarith) (by linarith) (fun i => by linarith [hKe i])
    (hpsd_of_psd K v t ((eig_le_iff_posSemidef hS t).mp (fun j => by linarith [hSe j])))
  have hq' : ∀ B : Matrix (Fin p) (Fin p) ℂ, (star v ⬝ᵥ (B *ᵥ v)).re = (M : ℝ)⁻¹ * qform B w := by
    intro B; rw [hv, quad_smul, hrr]
  rw [hq'] at hq
  have htx : t / x = 1 - (x - e1) / (2 * x) := by rw [ht]; field_simp; ring
  rw [htx] at hq
  refine ⟨hKe, hq, ?_⟩
  have h := sm_trace' ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K) hA v hB
  have hG : (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹).IsHermitian :=
    (isHermitian_smul_one_sub hK x).inv
  have hcim := hG.im_star_dotProduct_mulVec_self v
  simp only [RCLike.im_to_complex] at hcim
  have h2 := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.sub_im, Complex.one_im, hcim, sub_zero, zero_mul, Complex.sub_re,
    Complex.one_re] at h2
  rw [hq', hq'] at h2
  have hpos : 0 < 1 - (M : ℝ)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w := by
    have : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
    linarith
  rw [eq_div_iff hpos.ne']
  unfold resT
  rw [← sub_sub]
  linear_combination h2

/-- The per-coordinate constant. -/
noncomputable def condC (p M : ℕ) (x e1 : ℝ) : ℝ :=
  2 / ((x - e1) / (2 * x)) ^ 2 * ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 4) +
    8 * ((M : ℝ)⁻¹ * (p * ((x - e1)⁻¹) ^ 2)) ^ 2 / ((x - e1) / (2 * x)) ^ 4 * ((M : ℝ)⁻¹) ^ 2 *
      (p * ((x - e1)⁻¹) ^ 2)

theorem condC_nonneg (p M : ℕ) (x e1 : ℝ) : 0 ≤ condC p M x e1 := by
  unfold condC; positivity

open Classical in
/-- The conditional increment for fixed `K` (column `k` removed). -/
noncomputable def psiK {p : ℕ} (M : ℕ) (x e1 : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) (w : Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - (K + (M : ℂ)⁻¹ • vecMulVec w (star w))).PosSemidef then
    resT x (K + (M : ℂ)⁻¹ • vecMulVec w (star w)) - resT x K -
      (M : ℝ)⁻¹ * resT2 x K / (1 - min ((M : ℝ)⁻¹ * resT x K) (1 - (x - e1) / (2 * x) / 2))
  else 0

theorem integrable_qform_sq {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    Integrable (fun y => (qform B y - (trace B).re) ^ 2) (cgv n) := by
  by_cases h : ∑ i, hB.eigenvalues i ^ 2 = 0
  · have h0 : ∀ i, hB.eigenvalues i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (hB.eigenvalues j))).mp h i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have hf : (fun y => (qform B y - (trace B).re) ^ 2) = fun _ => (0 : ℝ) := by
      funext y
      rw [qform_eig hB, ← sum_eig_eq_trace hB]
      simp [h0]
    rw [hf]
    exact integrable_const _
  · exact Integrable.of_integral_ne_zero (by rw [integral_qform_sq hB]; exact h)

theorem cond_bound {p M : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x)
    {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) (hK0 : ∀ i, 0 ≤ hK.eigenvalues i) :
    ∫ w, psiK M x e1 K w ^ 2 ∂cgv p ≤ condC p M x e1 := by
  have hx0 : 0 < x := by linarith
  set κ := (x - e1) / (2 * x) with hκ
  have hκ0 : 0 < κ := div_pos (by linarith) (by linarith)
  set a := (x - e1)⁻¹ with ha
  set G := ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ with hGdef
  have hG : G.IsHermitian := (isHermitian_smul_one_sub hK x).inv
  have hGG : (G * G).IsHermitian := by have := hG.pow 2; rwa [sq] at this
  by_cases hKe : ∀ i, hK.eigenvalues i ≤ e1
  swap
  · have h0 : ∀ w, psiK M x e1 K w = 0 := by
      intro w
      unfold psiK
      rw [if_neg]
      intro hg
      exact hKe (good_step hM he1 hx hK hK0 w hg).1
    simp only [h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    exact condC_nonneg p M x e1
  have hne : ∀ i, hK.eigenvalues i ≠ x := fun i => ne_of_lt (by linarith [hKe i])
  have hT2 := res_diag hK x hne 2
  have hT4 := res_diag hK x hne 4
  rw [← hGdef] at hT2 hT4
  have b2 := sum_inv_pow_le (hK.eigenvalues) hx hKe 2
  have b4 := sum_inv_pow_le (hK.eigenvalues) hx hKe 4
  set U := (M : ℝ)⁻¹ * (p * a ^ 2) with hU
  have hr2 : resT2 x K = (trace (G * G)).re := rfl
  have hr1 : resT x K = (trace G).re := rfl
  have hG2 : (trace (G * G)).re = ∑ i, ((x - hK.eigenvalues i)⁻¹) ^ 2 := by rw [← hT2, sq]
  have hG4 : (trace ((G * G) * (G * G))).re = ∑ i, ((x - hK.eigenvalues i)⁻¹) ^ 4 := by
    rw [← hT4]; congr 2; noncomm_ring
  have hMi : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have hub0 : 0 ≤ (M : ℝ)⁻¹ * resT2 x K := by rw [hr2, hG2]; exact mul_nonneg hMi b2.1
  have hubU : (M : ℝ)⁻¹ * resT2 x K ≤ U := by
    rw [hr2, hG2, hU]; exact mul_le_mul_of_nonneg_left b2.2 hMi
  set α := 2 / κ ^ 2 * ((M : ℝ)⁻¹) ^ 2 with hα
  set β := 8 * U ^ 2 / κ ^ 4 * ((M : ℝ)⁻¹) ^ 2 with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have hpt : ∀ w, psiK M x e1 K w ^ 2 ≤
      α * (qform (G * G) w - (trace (G * G)).re) ^ 2 + β * (qform G w - (trace G).re) ^ 2 := by
    intro w
    unfold psiK
    split_ifs with hg
    · obtain ⟨-, hq, he⟩ := good_step hM he1 hx hK hK0 w hg
      rw [← hGdef] at hq he
      rw [he]
      refine (r_bound (u := (M : ℝ)⁻¹ * qform (G * G) w) (qb := (M : ℝ)⁻¹ * resT x K) hκ0 hq hub0 hubU).trans
        (le_of_eq ?_)
      rw [hr1, hr2, hα, hβ]
      ring
    · rw [zero_pow two_ne_zero]
      positivity
  have hI1 := (integrable_qform_sq hGG).const_mul α
  have hI2 := (integrable_qform_sq hG).const_mul β
  calc ∫ w, psiK M x e1 K w ^ 2 ∂cgv p
      ≤ ∫ w, (α * (qform (G * G) w - (trace (G * G)).re) ^ 2 + β * (qform G w - (trace G).re) ^ 2) ∂cgv p :=
        integral_mono_of_nonneg (ae_of_all _ (fun w => sq_nonneg _)) (hI1.add hI2) (ae_of_all _ hpt)
    _ = α * (trace ((G * G) * (G * G))).re + β * (trace (G * G)).re := by
        rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_qform_sq hGG,
          integral_qform_sq hG, sum_eig_sq_eq hGG, sum_eig_sq_eq hG]
    _ ≤ α * (p * a ^ 4) + β * (p * a ^ 2) := by
        rw [hG4, hG2]
        exact add_le_add (mul_le_mul_of_nonneg_left b4.2 hα0) (mul_le_mul_of_nonneg_left b2.2 hβ0)
    _ = condC p M x e1 := by rw [hα, hβ, hU, hκ, ha]; rfl

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

theorem measurable_resT2 {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] {p : ℕ}
    {f : α → Matrix (Fin p) (Fin p) ℂ} (hf : Continuous f) (x : ℝ) :
    Measurable (fun a => resT2 x (f a)) := by
  unfold resT2
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
    Complex.measurable_re.comp ((meas_inv_entry hf x i j).mul (meas_inv_entry hf x j i))))

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

open Classical in
/-- The leave-one-out proxy for coordinate `k`. -/
noncomputable def Phik {M p : ℕ} (x e1 : ℝ) (k : Fin M) (X : Fin M → Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat (Function.update X k 0)).PosSemidef then
    resT x (Smat (Function.update X k 0)) + (M : ℝ)⁻¹ * resT2 x (Smat (Function.update X k 0)) /
      (1 - min ((M : ℝ)⁻¹ * resT x (Smat (Function.update X k 0))) (1 - (x - e1) / (2 * x) / 2))
  else 0

/-- The bound for `Φ_k`. -/
noncomputable def bnd0 (p M : ℕ) (x e1 : ℝ) : ℝ :=
  p * (x - e1)⁻¹ + 2 * ((M : ℝ)⁻¹ * (p * ((x - e1)⁻¹) ^ 2)) / ((x - e1) / (2 * x))

theorem measurable_Ff {M p : ℕ} (x e1 : ℝ) : Measurable (fun X : Fin M → Fin p → ℂ => Ff x e1 X) := by
  unfold Ff
  exact Measurable.ite (((isClosed_good e1).preimage continuous_Smat).measurableSet)
    (measurable_resT continuous_Smat x) measurable_const

theorem continuous_Smat_upd {M p : ℕ} (k : Fin M) :
    Continuous (fun X : Fin M → Fin p → ℂ => Smat (Function.update X k 0)) :=
  continuous_Smat.comp (continuous_id.update k continuous_const)

theorem measurable_Phik {M p : ℕ} (x e1 : ℝ) (k : Fin M) :
    Measurable (fun X : Fin M → Fin p → ℂ => Phik x e1 k X) := by
  unfold Phik
  have hc := continuous_Smat_upd (p := p) k
  refine Measurable.ite (((isClosed_good e1).preimage hc).measurableSet) ?_ measurable_const
  refine (measurable_resT hc x).add (((measurable_resT2 hc x).const_mul _).div ?_)
  exact measurable_const.sub ((measurable_resT hc x).const_mul _ |>.min measurable_const)

theorem Ff_bound {M p : ℕ} {x e1 : ℝ} (hx : e1 < x) (X : Fin M → Fin p → ℂ) :
    |Ff x e1 X| ≤ p * (x - e1)⁻¹ := by
  have ha : 0 ≤ (p : ℝ) * (x - e1)⁻¹ := mul_nonneg (Nat.cast_nonneg p) (inv_nonneg.mpr (by linarith))
  unfold Ff
  split_ifs with hg
  · have hH := (Smat_psd X).isHermitian
    have hb := res_bounds hH hx ((eig_le_iff_posSemidef hH e1).mpr hg)
    rw [abs_of_nonneg hb.1]; exact hb.2.1
  · simpa using ha

theorem Phik_bound {M p : ℕ} {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M) (X : Fin M → Fin p → ℂ) :
    0 ≤ Phik x e1 k X ∧ Phik x e1 k X ≤ bnd0 p M x e1 := by
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
  have hb0 : 0 ≤ bnd0 p M x e1 := by
    unfold bnd0
    have : 0 ≤ (x - e1)⁻¹ := inv_nonneg.mpr (by linarith)
    positivity
  unfold Phik
  split_ifs with hg
  · set K := Smat (Function.update X k 0)
    have hH := (Smat_psd (Function.update X k 0)).isHermitian
    have hb := res_bounds hH hx ((eig_le_iff_posSemidef hH e1).mpr hg)
    set qt := min ((M : ℝ)⁻¹ * resT x K) (1 - (x - e1) / (2 * x) / 2)
    have hqt : (x - e1) / (2 * x) / 2 ≤ 1 - qt := by
      have := min_le_right ((M : ℝ)⁻¹ * resT x K) (1 - (x - e1) / (2 * x) / 2); linarith
    have hMi : 0 ≤ (M : ℝ)⁻¹ := by positivity
    have hn0 : 0 ≤ (M : ℝ)⁻¹ * resT2 x K := mul_nonneg hMi hb.2.2.1
    have hnU : (M : ℝ)⁻¹ * resT2 x K ≤ (M : ℝ)⁻¹ * (p * ((x - e1)⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_left hb.2.2.2 hMi
    have hd : (M : ℝ)⁻¹ * resT2 x K / (1 - qt) ≤
        (M : ℝ)⁻¹ * (p * ((x - e1)⁻¹) ^ 2) / ((x - e1) / (2 * x) / 2) :=
      div_le_div₀ (le_trans hn0 hnU) hnU (by positivity) hqt
    have hd0 : 0 ≤ (M : ℝ)⁻¹ * resT2 x K / (1 - qt) := div_nonneg hn0 (by linarith)
    have e : (M : ℝ)⁻¹ * (p * ((x - e1)⁻¹) ^ 2) / ((x - e1) / (2 * x) / 2) =
        2 * ((M : ℝ)⁻¹ * (p * ((x - e1)⁻¹) ^ 2)) / ((x - e1) / (2 * x)) := by
      field_simp
    unfold bnd0
    constructor
    · linarith [hb.1]
    · linarith [hb.2.1]
  · exact ⟨le_refl 0, hb0⟩

open Classical in
/-- On the good event, `F - Φ_k` is the conditional increment `psiK`. -/
theorem F_sub_Phik {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M)
    (X : Fin M → Fin p → ℂ) :
    (if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then Ff x e1 X - Phik x e1 k X else 0) =
      psiK M x e1 (Smat (Function.update X k 0)) (X k) := by
  have hS : Smat X = Smat (Function.update X k 0) + (M : ℂ)⁻¹ • vecMulVec (X k) (star (X k)) := by
    have := Smat_update X k (X k)
    rwa [Function.update_eq_self] at this
  have hpsd := Smat_psd (Function.update X k 0)
  unfold psiK
  rw [← hS]
  split_ifs with hg
  · have hK0 : ∀ i, 0 ≤ hpsd.isHermitian.eigenvalues i := hpsd.eigenvalues_nonneg
    rw [hS] at hg
    have hKe := (good_step hM he1 hx hpsd.isHermitian hK0 (X k) hg).1
    have hgK := (eig_le_iff_posSemidef hpsd.isHermitian e1).mp hKe
    rw [← hS] at hg
    unfold Ff Phik
    rw [if_pos hg, if_pos hgK]
    ring
  · rfl

theorem Ff_sq_le {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M)
    (X : Fin M → Fin p → ℂ) :
    (Ff x e1 X - Phik x e1 k X) ^ 2 ≤ psiK M x e1 (Smat (Function.update X k 0)) (X k) ^ 2 +
      Set.indicator {X : Fin M → Fin p → ℂ | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef}
        (fun _ => bnd0 p M x e1 ^ 2) X := by
  rw [← F_sub_Phik hM he1 hx k X]
  have hb := Phik_bound (M := M) he1 hx k X
  by_cases hg : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef
  · rw [if_pos hg, Set.indicator_of_notMem (by simpa using hg), add_zero]
  · rw [if_neg hg, Set.indicator_of_mem (by simpa using hg)]
    have hF : Ff x e1 X = 0 := by unfold Ff; rw [if_neg hg]
    rw [hF, zero_sub, neg_sq, zero_pow two_ne_zero, zero_add]
    exact pow_le_pow_left₀ hb.1 hb.2 2

theorem Phik_update {M p : ℕ} (x e1 : ℝ) (k : Fin M) (X : Fin M → Fin p → ℂ) (w : Fin p → ℂ) :
    Phik x e1 k (Function.update X k w) = Phik x e1 k X := by
  unfold Phik
  rw [Function.update_idem]

open Classical in
/-- Variance of the truncated trace (Efron-Stein with leave-one-out proxies). -/
theorem var_Ff {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) :
    ∫ X, (Ff x e1 X - ∫ Y, Ff x e1 Y ∂SpikedWishart.SoftEdge.sampleLaw M p) ^ 2
        ∂SpikedWishart.SoftEdge.sampleLaw M p ≤
      M * (condC p M x e1 + bnd0 p M x e1 ^ 2 * (SpikedWishart.SoftEdge.sampleLaw M p).real
        {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef}) := by
  have := Weyl.isProb_cg
  have hν : IsProbabilityMeasure (cgv p) := by unfold cgv; infer_instance
  have hlaw : SpikedWishart.SoftEdge.sampleLaw M p = Measure.pi fun _ : Fin M => cgv p := rfl
  rw [hlaw]
  set π := Measure.pi fun _ : Fin M => cgv p
  set A := (p : ℝ) * (x - e1)⁻¹ with hA
  set B := bnd0 p M x e1 with hB
  set bad := {X : Fin M → Fin p → ℂ | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef}
  have hbad : MeasurableSet bad :=
    (((isClosed_good e1).preimage continuous_Smat).measurableSet).compl
  have hFm := measurable_Ff (M := M) (p := p) x e1
  have hFb : ∀ X : Fin M → Fin p → ℂ, |Ff x e1 X| ≤ A := Ff_bound hx
  have hB0 : 0 ≤ B := le_trans (Phik_bound (M := M) (p := p) he1 hx ⟨0, hM⟩ 0).1
    (Phik_bound (M := M) (p := p) he1 hx ⟨0, hM⟩ 0).2
  have hPb : ∀ k X, |Phik x e1 k X| ≤ B := fun k X => by
    rw [abs_of_nonneg (Phik_bound he1 hx k X).1]; exact (Phik_bound he1 hx k X).2
  have hstep : ∀ k : Fin M, ∫ X, (Ff x e1 X - ∫ w, Ff x e1 (Function.update X k w) ∂cgv p) ^ 2 ∂π ≤
      condC p M x e1 + B ^ 2 * π.real bad := by
    intro k
    have hPm := measurable_Phik (M := M) (p := p) x e1 k
    refine (es_proxy (cgv p) (fun X => Ff x e1 X) (fun X => Phik x e1 k X) A B hFm hFb hPm (hPb k) k
      (fun X w => Phik_update x e1 k X w)).trans ?_
    -- the good part
    set Gk : (Fin M → Fin p → ℂ) → ℝ := fun X =>
      if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then Ff x e1 X - Phik x e1 k X else 0
      with hGk
    have hs : MeasurableSet {X : Fin M → Fin p → ℂ | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef} :=
      ((isClosed_good e1).preimage continuous_Smat).measurableSet
    have hGm : Measurable Gk := Measurable.ite hs (hFm.sub hPm) measurable_const
    have hGb : ∀ X, |Gk X| ≤ A + B := by
      intro X; simp only [hGk]; split_ifs
      · exact (abs_sub _ _).trans (add_le_add (hFb X) (hPb k X))
      · simp only [abs_zero]; linarith [abs_nonneg (Ff x e1 X), hFb X, hB0]
    have hG2 : ∫ X, Gk X ^ 2 ∂π ≤ condC p M x e1 := by
      rw [resample (cgv p) (fun X => Gk X ^ 2) ((A + B) ^ 2) (hGm.pow_const 2)
        (fun X => by rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hGb X) 2) k]
      have hin : ∀ X : Fin M → Fin p → ℂ, ∫ w, Gk (Function.update X k w) ^ 2 ∂cgv p ≤ condC p M x e1 := by
        intro X
        have hpsd := Smat_psd (Function.update X k 0)
        have e : ∀ w, Gk (Function.update X k w) = psiK M x e1 (Smat (Function.update X k 0)) w := by
          intro w
          rw [hGk]
          beta_reduce
          rw [F_sub_Phik hM he1 hx k (Function.update X k w), Function.update_idem, Function.update_self]
        simp only [e]
        exact cond_bound hM he1 hx hpsd.isHermitian hpsd.eigenvalues_nonneg
      calc ∫ X, ∫ w, Gk (Function.update X k w) ^ 2 ∂cgv p ∂π ≤ ∫ X, condC p M x e1 ∂π :=
            integral_mono_of_nonneg (ae_of_all _ (fun X => integral_nonneg (fun w => sq_nonneg _)))
              (integrable_const _) (ae_of_all _ hin)
        _ = condC p M x e1 := by rw [integral_const, probReal_univ, one_smul]
    have hpt : ∀ X, (Ff x e1 X - Phik x e1 k X) ^ 2 ≤ Gk X ^ 2 + bad.indicator (fun _ => B ^ 2) X := by
      intro X
      have := Ff_sq_le hM he1 hx k X
      rw [← F_sub_Phik hM he1 hx k X] at this
      exact this
    have hI1 : Integrable (fun X => Gk X ^ 2) π :=
      iob (hGm.pow_const 2) ((A + B) ^ 2)
        (fun X => by rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hGb X) 2)
    have hI2 : Integrable (fun X => bad.indicator (fun _ => B ^ 2) X) π :=
      (integrable_const _).indicator hbad
    calc ∫ X, (Ff x e1 X - Phik x e1 k X) ^ 2 ∂π
        ≤ ∫ X, (Gk X ^ 2 + bad.indicator (fun _ => B ^ 2) X) ∂π :=
          integral_mono_of_nonneg (ae_of_all _ (fun X => sq_nonneg _)) (hI1.add hI2) (ae_of_all _ hpt)
      _ = ∫ X, Gk X ^ 2 ∂π + π.real bad * B ^ 2 := by
          rw [integral_add hI1 hI2, integral_indicator_const _ hbad, smul_eq_mul]
      _ ≤ condC p M x e1 + B ^ 2 * π.real bad := by rw [mul_comm (π.real bad)]; linarith
  calc ∫ X, (Ff x e1 X - ∫ Y, Ff x e1 Y ∂π) ^ 2 ∂π
      ≤ ∑ k, ∫ X, (Ff x e1 X - ∫ w, Ff x e1 (Function.update X k w) ∂cgv p) ^ 2 ∂π :=
        efron_stein (cgv p) M (fun X => Ff x e1 X) A hFm hFb
    _ ≤ ∑ _k : Fin M, (condC p M x e1 + B ^ 2 * π.real bad) := Finset.sum_le_sum (fun k _ => hstep k)
    _ = M * (condC p M x e1 + B ^ 2 * π.real bad) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Q2

end

-- ===== from Q2f.lean =====
section

namespace Q2

theorem trace_mul_vmv {p : ℕ} (G : Matrix (Fin p) (Fin p) ℂ) (v : Fin p → ℂ) :
    trace (G * vecMulVec v (star v)) = star v ⬝ᵥ (G *ᵥ v) := by
  simp only [trace, diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem Smat_sum {M p : ℕ} (hM : 0 < M) (X : Fin M → Fin p → ℂ) :
    Smat X = ∑ k, vecMulVec ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) • X k) (star ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) • X k)) := by
  simp_rw [vmv_smul hM]
  ext i j
  rw [Smat_apply, Matrix.sum_apply]
  simp [vecMulVec_apply, Finset.mul_sum]

/-- The leave-one-out quadratic form `q_k = M⁻¹ X_kᴴ (x - S_k)⁻¹ X_k`. -/
noncomputable def qk {M p : ℕ} (x : ℝ) (X : Fin M → Fin p → ℂ) (k : Fin M) : ℝ :=
  (M : ℝ)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat (Function.update X k 0))⁻¹) (X k)

theorem Smat_split {M p : ℕ} (X : Fin M → Fin p → ℂ) (k : Fin M) :
    Smat X = Smat (Function.update X k 0) + (M : ℂ)⁻¹ • vecMulVec (X k) (star (X k)) := by
  have := Smat_update X k (X k)
  rwa [Function.update_eq_self] at this

/-- Self-consistent identity on the good event: `x tr G - p = Σ_k q_k/(1-q_k)`. -/
theorem selfcons {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (X : Fin M → Fin p → ℂ)
    (hg : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef) :
    x * resT x (Smat X) - p = ∑ k, qk x X k / (1 - qk x X k) := by
  have hS := (Smat_psd X).isHermitian
  have hSe := (eig_le_iff_posSemidef hS e1).mpr hg
  have hdet := unit_of_eig hS (fun j => by linarith [hSe j])
  set G := ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X)⁻¹ with hGdef
  have hGH : G.IsHermitian := (isHermitian_smul_one_sub hS x).inv
  have h2 := congrArg trace (G_mul_S (Smat X) (x : ℂ) hdet)
  rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at h2
  set r : ℝ := (Real.sqrt M)⁻¹ with hr
  have hrr : r * r = (M : ℝ)⁻¹ := by
    rw [hr, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg M)]
  have hsum : trace (G * Smat X) = ∑ k, star ((r : ℂ) • X k) ⬝ᵥ (G *ᵥ ((r : ℂ) • X k)) := by
    conv_lhs => rw [Smat_sum hM X]
    rw [Matrix.mul_sum, trace_sum]
    simp only [trace_mul_vmv]
    rfl
  have hk : ∀ k, (star ((r : ℂ) • X k) ⬝ᵥ (G *ᵥ ((r : ℂ) • X k))).re = qk x X k / (1 - qk x X k) := by
    intro k
    set K := Smat (Function.update X k 0) with hK
    set v : Fin p → ℂ := (r : ℂ) • X k with hv
    have hpsdK := Smat_psd (Function.update X k 0)
    have hS' := Smat_split X k
    have hvv : vecMulVec v (star v) = (M : ℂ)⁻¹ • vecMulVec (X k) (star (X k)) := vmv_smul hM (X k)
    have hg' := hg
    rw [hS'] at hg'
    obtain ⟨hKe, hq, -⟩ := good_step hM he1 hx hpsdK.isHermitian hpsdK.eigenvalues_nonneg (X k) hg'
    have hA : IsUnit ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K).det :=
      unit_of_eig hpsdK.isHermitian (fun i => by linarith [hKe i])
    have hKS : Smat X = K + vecMulVec v (star v) := by rw [hvv]; exact hS'
    have hB : IsUnit (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K) - vecMulVec v (star v)).det := by
      rw [sub_sub, ← hKS]; exact hdet
    have hsm := sm_vec ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K) hA v hB
    rw [sub_sub, ← hKS] at hsm
    have hdot := congrArg (fun z => star v ⬝ᵥ z) hsm
    simp only [dotProduct_smul, smul_eq_mul] at hdot
    have hAH : (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹).IsHermitian :=
      (isHermitian_smul_one_sub hpsdK.isHermitian x).inv
    have hcim := hAH.im_star_dotProduct_mulVec_self v
    simp only [RCLike.im_to_complex] at hcim
    have hcre : (star v ⬝ᵥ (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ *ᵥ v)).re = qk x X k := by
      rw [hv, quad_smul, hrr]; rfl
    have h3 := congrArg Complex.re hdot
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hcim,
      sub_zero, zero_mul, hcre] at h3
    have hpos : 0 < 1 - qk x X k := by
      have : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
      have hq' : qk x X k ≤ 1 - (x - e1) / (2 * x) := hq
      linarith
    rw [eq_div_iff hpos.ne']
    linarith
  have h4 := congrArg Complex.re (hsum.symm.trans h2)
  rw [Complex.re_sum] at h4
  simp only [hk, Complex.sub_re, Complex.re_ofReal_mul, Complex.natCast_re] at h4
  rw [h4]
  rfl

theorem qform_diag {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (d : Fin p → ℝ) (w : Fin p → ℂ) :
    qform (U * diagonal (fun i => (d i : ℂ)) * star U) w = ∑ i, d i * Complex.normSq ((star U *ᵥ w) i) := by
  unfold qform
  rw [quad_conj, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_left_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- `0 <= wᴴ G w` and `wᴴ G² w <= (x - e1)⁻¹ wᴴ G w` when `eig K <= e1 < x`. -/
theorem qform_bounds {p : ℕ} {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian) {x e1 : ℝ} (hx : e1 < x)
    (hKe : ∀ i, hK.eigenvalues i ≤ e1) (w : Fin p → ℂ) :
    0 ≤ qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w ∧
    0 ≤ qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ *
      ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w ∧
    qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ *
      ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w ≤
      (x - e1)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w := by
  have hne : ∀ i, hK.eigenvalues i ≠ x := fun i => ne_of_lt (by linarith [hKe i])
  rw [inv_eig hK x hne]
  set U := (hK.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) with hUdef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hK.eigenvectorUnitary
  set d : Fin p → ℝ := fun i => (x - hK.eigenvalues i)⁻¹ with hd
  have hsq : U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U * (U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U) =
      U * diagonal (fun i => ((d i * d i : ℝ) : ℂ)) * star U := by
    calc U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U * (U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U)
        = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * (star U * U) * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun i => ((d i * d i : ℝ) : ℂ)) * star U := by
          rw [hUU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
          simp only [Complex.ofReal_mul]
  rw [hsq, qform_diag, qform_diag]
  have h0 : ∀ i, 0 ≤ d i := fun i => inv_nonneg.mpr (by linarith [hKe i])
  have h1 : ∀ i, d i ≤ (x - e1)⁻¹ := fun i => inv_anti₀ (by linarith) (by linarith [hKe i])
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (h0 i) (Complex.normSq_nonneg _)),
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (h0 i) (h0 i)) (Complex.normSq_nonneg _)), ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h1 i) (h0 i)) (Complex.normSq_nonneg _)

/-- On the good event the leave-one-out trace moves by at most `(x-e1)⁻¹/κ`, and `0 <= q_k <= 1-κ`. -/
theorem resT_loo {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (X : Fin M → Fin p → ℂ)
    (hg : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef) (k : Fin M) :
    0 ≤ qk x X k ∧ qk x X k ≤ 1 - (x - e1) / (2 * x) ∧
    0 ≤ resT x (Smat X) - resT x (Smat (Function.update X k 0)) ∧
    resT x (Smat X) - resT x (Smat (Function.update X k 0)) ≤ (x - e1)⁻¹ / ((x - e1) / (2 * x)) := by
  have hpsdK := Smat_psd (Function.update X k 0)
  have hg' := hg
  rw [Smat_split X k] at hg'
  obtain ⟨hKe, hq, he⟩ := good_step hM he1 hx hpsdK.isHermitian hpsdK.eigenvalues_nonneg (X k) hg'
  have hb := qform_bounds hpsdK.isHermitian hx hKe (X k)
  have hMi : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have hκ : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
  have hq0 : 0 ≤ qk x X k := mul_nonneg hMi hb.1
  have hq1 : qk x X k ≤ 1 - (x - e1) / (2 * x) := hq
  rw [← Smat_split X k] at he
  have hden : (x - e1) / (2 * x) ≤ 1 - qk x X k := by linarith
  have hu0 : 0 ≤ (M : ℝ)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat (Function.update X k 0))⁻¹ *
      ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat (Function.update X k 0))⁻¹) (X k) := mul_nonneg hMi hb.2.1
  have hu1 : (M : ℝ)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat (Function.update X k 0))⁻¹ *
      ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat (Function.update X k 0))⁻¹) (X k) ≤ (x - e1)⁻¹ := by
    have hq1' : qk x X k ≤ 1 := by linarith
    calc _ ≤ (M : ℝ)⁻¹ * ((x - e1)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
          Smat (Function.update X k 0))⁻¹) (X k)) := mul_le_mul_of_nonneg_left hb.2.2 hMi
      _ = (x - e1)⁻¹ * qk x X k := by unfold qk; ring
      _ ≤ (x - e1)⁻¹ * 1 := mul_le_mul_of_nonneg_left hq1' (inv_nonneg.mpr (by linarith))
      _ = (x - e1)⁻¹ := mul_one _
  refine ⟨hq0, hq1, ?_, ?_⟩
  · rw [he]; exact div_nonneg hu0 (by linarith)
  · rw [he]; exact div_le_div₀ (inv_nonneg.mpr (by linarith)) hu1 hκ hden

end Q2

end

-- ===== from Q2g.lean =====
section

namespace Q2

theorem continuous_qform {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) : Continuous (fun y : Fin n → ℂ => qform B y) := by
  unfold qform
  exact Complex.continuous_re.comp ((continuous_id.star).dotProduct (continuous_const.matrix_mulVec continuous_id))

theorem integrable_qform {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    Integrable (fun y => qform B y) (cgv n) := by
  have := Weyl.isProb_cg
  have hν : IsProbabilityMeasure (cgv n) := by unfold cgv; infer_instance
  set c := (trace B).re
  refine Integrable.mono' ((((integrable_qform_sq hB).add (integrable_const 1)).div_const 2).add
    (integrable_const |c|)) (continuous_qform B).aestronglyMeasurable (ae_of_all _ (fun y => ?_))
  rw [Real.norm_eq_abs]
  have h1 : |qform B y - c| ≤ ((qform B y - c) ^ 2 + 1) / 2 := by
    nlinarith [sq_nonneg (|qform B y - c| - 1), sq_abs (qform B y - c), abs_nonneg (qform B y - c)]
  have h2 : |qform B y| ≤ |qform B y - c| + |c| := by
    have := abs_add_le (qform B y - c) c
    rwa [sub_add_cancel] at this
  simp only [Pi.add_apply]
  linarith

theorem ind_sq_le {α : Type*} (s : Set α) (f : α → ℝ) (w : α) : (s.indicator f w) ^ 2 ≤ (f w) ^ 2 := by
  by_cases h : w ∈ s
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, zero_pow two_ne_zero]; exact sq_nonneg _

theorem ind_abs_half {α : Type*} (s : Set α) (f : α → ℝ) (w : α) :
    |s.indicator f w| ≤ (f w ^ 2 + s.indicator (fun _ => (1 : ℝ)) w) / 2 := by
  by_cases h : w ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    nlinarith [sq_nonneg (|f w| - 1), sq_abs (f w), abs_nonneg (f w)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, abs_zero, add_zero]; positivity

theorem ind_one_abs {α : Type*} (s : Set α) (w : α) : |s.indicator (fun _ => (1 : ℝ)) w| ≤ 1 := by
  by_cases h : w ∈ s
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simp

/-- The centred leave-one-out form `M⁻¹(wᴴ G_K w - tr G_K)`. -/
noncomputable def Mq {p : ℕ} (M : ℕ) (x : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) (w : Fin p → ℂ) : ℝ :=
  (M : ℝ)⁻¹ * qform (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹) w - (M : ℝ)⁻¹ * resT x K

theorem Mq_moments {p : ℕ} (M : ℕ) {x e1 : ℝ} (hx : e1 < x) {K : Matrix (Fin p) (Fin p) ℂ} (hK : K.IsHermitian)
    (hKe : ∀ i, hK.eigenvalues i ≤ e1) :
    Integrable (fun w => Mq M x K w) (cgv p) ∧ Integrable (fun w => Mq M x K w ^ 2) (cgv p) ∧
    ∫ w, Mq M x K w ∂cgv p = 0 ∧ ∫ w, Mq M x K w ^ 2 ∂cgv p ≤ ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) := by
  have := Weyl.isProb_cg
  have hν : IsProbabilityMeasure (cgv p) := by unfold cgv; infer_instance
  set G := ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - K)⁻¹ with hGdef
  have hG : G.IsHermitian := (isHermitian_smul_one_sub hK x).inv
  have hr : resT x K = (trace G).re := rfl
  have hI := integrable_qform hG
  have hI2 := integrable_qform_sq hG
  have e2 : (fun w => Mq M x K w ^ 2) = fun w => ((M : ℝ)⁻¹) ^ 2 * (qform G w - (trace G).re) ^ 2 := by
    funext w; unfold Mq; rw [hr]; ring
  have hb := res_bounds hK hx hKe
  refine ⟨(hI.const_mul _).sub (integrable_const _), ?_, ?_, ?_⟩
  · rw [e2]; exact hI2.const_mul _
  · unfold Mq
    rw [integral_sub (hI.const_mul _) (integrable_const _), integral_const_mul, integral_qform hG, integral_const,
      probReal_univ, one_smul, hr, sub_self]
  · rw [e2, integral_const_mul, integral_qform_sq hG, sum_eig_sq_eq hG]
    have : (trace (G * G)).re = resT2 x K := rfl
    rw [this]
    exact mul_le_mul_of_nonneg_left hb.2.2.2 (by positivity)

open Classical in
/-- `δ_k = 1_Good (q_k - M⁻¹ resT S_k)`. -/
noncomputable def dk {M p : ℕ} (x e1 : ℝ) (k : Fin M) (X : Fin M → Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then
    qk x X k - (M : ℝ)⁻¹ * resT x (Smat (Function.update X k 0)) else 0

open Classical in
theorem dk_update {M p : ℕ} (x e1 : ℝ) (k : Fin M) (X : Fin M → Fin p → ℂ) (w : Fin p → ℂ) :
    dk x e1 k (Function.update X k w) =
      Set.indicator {w : Fin p → ℂ | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        (Smat (Function.update X k 0) + (M : ℂ)⁻¹ • vecMulVec w (star w))).PosSemidef}
        (fun w => Mq M x (Smat (Function.update X k 0)) w) w := by
  unfold dk qk
  rw [Function.update_idem, Function.update_self, Smat_update X k w]
  by_cases h : ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
      (Smat (Function.update X k 0) + (M : ℂ)⁻¹ • vecMulVec w (star w))).PosSemidef
  · rw [if_pos h, Set.indicator_of_mem (show w ∈ {w : Fin p → ℂ | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        (Smat (Function.update X k 0) + (M : ℂ)⁻¹ • vecMulVec w (star w))).PosSemidef} from h)]
    rfl
  · rw [if_neg h, Set.indicator_of_notMem (show w ∉ {w : Fin p → ℂ | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        (Smat (Function.update X k 0) + (M : ℂ)⁻¹ • vecMulVec w (star w))).PosSemidef} from h)]

theorem measurable_coord {M p : ℕ} (k : Fin M) (i : Fin p) : Measurable (fun X : Fin M → Fin p → ℂ => X k i) :=
  (measurable_pi_apply i).comp (measurable_pi_apply k)

theorem measurable_qk {M p : ℕ} (x : ℝ) (k : Fin M) : Measurable (fun X : Fin M → Fin p → ℂ => qk x X k) := by
  unfold qk qform
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.re_sum]
  refine Measurable.const_mul (Finset.measurable_sum _ (fun i _ => Complex.measurable_re.comp ?_)) _
  refine (Complex.continuous_conj.measurable.comp (measurable_coord k i)).mul
    (Finset.measurable_sum _ (fun j _ => ?_))
  exact (meas_inv_entry (continuous_Smat_upd k) x i j).mul (measurable_coord k j)

theorem measurable_dk {M p : ℕ} (x e1 : ℝ) (k : Fin M) : Measurable (fun X : Fin M → Fin p → ℂ => dk x e1 k X) := by
  unfold dk
  exact Measurable.ite (((isClosed_good e1).preimage continuous_Smat).measurableSet)
    ((measurable_qk x k).sub ((measurable_resT (continuous_Smat_upd k) x).const_mul _)) measurable_const

theorem dk_bound {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M)
    (X : Fin M → Fin p → ℂ) : |dk x e1 k X| ≤ 1 + (M : ℝ)⁻¹ * (p * (x - e1)⁻¹) := by
  have hMi : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have h0 : 0 ≤ (M : ℝ)⁻¹ * (p * (x - e1)⁻¹) :=
    mul_nonneg hMi (mul_nonneg (Nat.cast_nonneg p) (inv_nonneg.mpr (by linarith)))
  unfold dk
  split_ifs with hg
  · have hl := resT_loo hM he1 hx X hg k
    have hpsdK := Smat_psd (Function.update X k 0)
    have hg' := hg
    rw [Smat_split X k] at hg'
    have hKe := (good_step hM he1 hx hpsdK.isHermitian hpsdK.eigenvalues_nonneg (X k) hg').1
    have hb := res_bounds hpsdK.isHermitian hx hKe
    have h1 : 0 ≤ (M : ℝ)⁻¹ * resT x (Smat (Function.update X k 0)) := mul_nonneg hMi hb.1
    have h2 : (M : ℝ)⁻¹ * resT x (Smat (Function.update X k 0)) ≤ (M : ℝ)⁻¹ * (p * (x - e1)⁻¹) :=
      mul_le_mul_of_nonneg_left hb.2.1 hMi
    have hκ : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
    rw [abs_le]
    constructor <;> linarith [hl.1, hl.2.1]
  · rw [abs_zero]; linarith

/-- (B): `E δ_k² <= M⁻² p (x-e1)⁻²`. -/
theorem dk_sq {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M) :
    ∫ X, dk x e1 k X ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p ≤ ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) := by
  have := Weyl.isProb_cg
  have hν : IsProbabilityMeasure (cgv p) := by unfold cgv; infer_instance
  have hlaw : SpikedWishart.SoftEdge.sampleLaw M p = Measure.pi fun _ : Fin M => cgv p := rfl
  rw [hlaw]
  set D := 1 + (M : ℝ)⁻¹ * (p * (x - e1)⁻¹)
  have hb : ∀ X : Fin M → Fin p → ℂ, |dk x e1 k X ^ 2| ≤ D ^ 2 := fun X => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (dk_bound hM he1 hx k X) 2
  rw [resample (cgv p) (fun X => dk x e1 k X ^ 2) (D ^ 2) ((measurable_dk x e1 k).pow_const 2) hb k]
  have hin : ∀ X : Fin M → Fin p → ℂ, ∫ w, dk x e1 k (Function.update X k w) ^ 2 ∂cgv p ≤
      ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) := by
    intro X
    simp only [dk_update]
    have hpsdK := Smat_psd (Function.update X k 0)
    by_cases hKe : ∀ i, hpsdK.isHermitian.eigenvalues i ≤ e1
    · obtain ⟨-, hI2, -, hm2⟩ := Mq_moments M hx hpsdK.isHermitian hKe
      exact le_trans (integral_mono_of_nonneg (ae_of_all _ (fun w => sq_nonneg _)) hI2
        (ae_of_all _ (fun w => ind_sq_le _ _ w))) hm2
    · have h0 : ∀ w : Fin p → ℂ, Set.indicator {w : Fin p → ℂ | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
          (Smat (Function.update X k 0) + (M : ℂ)⁻¹ • vecMulVec w (star w))).PosSemidef}
          (fun w => Mq M x (Smat (Function.update X k 0)) w) w = 0 := by
        intro w
        refine Set.indicator_of_notMem (fun hg => hKe ?_) _
        exact (good_step hM he1 hx hpsdK.isHermitian hpsdK.eigenvalues_nonneg w hg).1
      simp only [h0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
      positivity
  calc ∫ X, ∫ w, dk x e1 k (Function.update X k w) ^ 2 ∂cgv p ∂(Measure.pi fun _ : Fin M => cgv p)
      ≤ ∫ X, ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) ∂(Measure.pi fun _ : Fin M => cgv p) :=
        integral_mono_of_nonneg (ae_of_all _ (fun X => integral_nonneg (fun w => sq_nonneg _)))
          (integrable_const _) (ae_of_all _ hin)
    _ = _ := by rw [integral_const, probReal_univ, one_smul]

/-- (A): `|E δ_k| <= (M⁻² p (x-e1)⁻² + P(Bad))/2`. -/
theorem dk_mean {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M) :
    |∫ X, dk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p| ≤
      (((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) + (SpikedWishart.SoftEdge.sampleLaw M p).real
        {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef}) / 2 := by
  have := Weyl.isProb_cg
  have hν : IsProbabilityMeasure (cgv p) := by unfold cgv; infer_instance
  have hlaw : SpikedWishart.SoftEdge.sampleLaw M p = Measure.pi fun _ : Fin M => cgv p := rfl
  rw [hlaw]
  set π := Measure.pi fun _ : Fin M => cgv p
  set bad := {X : Fin M → Fin p → ℂ | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef}
  have hbad : MeasurableSet bad := (((isClosed_good e1).preimage continuous_Smat).measurableSet).compl
  set D := 1 + (M : ℝ)⁻¹ * (p * (x - e1)⁻¹)
  set V := ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2)
  rw [resample (cgv p) (fun X => dk x e1 k X) D (measurable_dk x e1 k) (dk_bound hM he1 hx k) k]
  set J : (Fin M → Fin p → ℂ) → ℝ := fun X => ∫ w, bad.indicator (fun _ => (1 : ℝ)) (Function.update X k w) ∂cgv p
  have hJm : Measurable J := measurable_Ek (cgv p) _ ((measurable_const.indicator hbad)) k
  have hJ : ∫ X, J X ∂π = π.real bad := by
    have := resample (cgv p) (fun X => bad.indicator (fun _ => (1 : ℝ)) X) 1 (measurable_const.indicator hbad)
      (fun X => ind_one_abs bad X) k
    rw [← this, integral_indicator_const _ hbad, smul_eq_mul, mul_one]
  have hin : ∀ X : Fin M → Fin p → ℂ, |∫ w, dk x e1 k (Function.update X k w) ∂cgv p| ≤ (V + J X) / 2 := by
    intro X
    simp only [dk_update]
    have hpsdK := Smat_psd (Function.update X k 0)
    set K := Smat (Function.update X k 0) with hKdef
    set gs := {w : Fin p → ℂ | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
          (K + (M : ℂ)⁻¹ • vecMulVec w (star w))).PosSemidef} with hgsdef
    have hgs : MeasurableSet gs := by
      have hv : Continuous (fun w : Fin p → ℂ => vecMulVec w (star w)) := by
        refine continuous_pi (fun i => continuous_pi (fun j => ?_))
        simp only [vecMulVec_apply, Pi.star_apply]
        exact (continuous_apply i).mul (continuous_apply j).star
      have hc : Continuous (fun w : Fin p → ℂ => K + (M : ℂ)⁻¹ • vecMulVec w (star w)) :=
        continuous_const.add (hv.const_smul ((M : ℂ)⁻¹))
      exact ((isClosed_good e1).preimage hc).measurableSet
    have hJX : J X = (cgv p).real gsᶜ := by
      rw [show (cgv p).real gsᶜ = ∫ w, gsᶜ.indicator (fun _ => (1 : ℝ)) w ∂cgv p by
        rw [integral_indicator_const _ hgs.compl, smul_eq_mul, mul_one]]
      refine integral_congr_ae (ae_of_all _ (fun w => ?_))
      beta_reduce
      have hmem : Function.update X k w ∈ bad ↔ w ∈ gsᶜ := by
        rw [Set.mem_compl_iff, hgsdef, Set.mem_setOf_eq, Set.mem_setOf_eq, Smat_update X k w]
      by_cases h : w ∈ gsᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mpr h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.mp h'))]
    have hJ0 : 0 ≤ J X := by rw [hJX]; exact measureReal_nonneg
    have hV0 : 0 ≤ V := by positivity
    by_cases hKe : ∀ i, hpsdK.isHermitian.eigenvalues i ≤ e1
    · obtain ⟨hI1, hI2, hm1, hm2⟩ := Mq_moments M hx hpsdK.isHermitian hKe
      have hsplit : ∫ w, gs.indicator (fun w => Mq M x K w) w ∂cgv p =
          - ∫ w, gsᶜ.indicator (fun w => Mq M x K w) w ∂cgv p := by
        have h := integral_add (hI1.indicator hgs) (hI1.indicator hgs.compl)
        rw [show (fun w => gs.indicator (fun w => Mq M x K w) w + gsᶜ.indicator (fun w => Mq M x K w) w) =
          fun w => Mq M x K w from funext (fun w => Set.indicator_self_add_compl_apply gs _ w), hm1] at h
        linarith
      rw [hsplit, abs_neg]
      have hpt : ∀ w, |gsᶜ.indicator (fun w => Mq M x K w) w| ≤
          (Mq M x K w ^ 2 + gsᶜ.indicator (fun _ => (1 : ℝ)) w) / 2 := fun w => ind_abs_half _ _ w
      have hI3 : Integrable (fun w => (Mq M x K w ^ 2 + gsᶜ.indicator (fun _ => (1 : ℝ)) w) / 2) (cgv p) :=
        (hI2.add ((integrable_const _).indicator hgs.compl)).div_const 2
      calc |∫ w, gsᶜ.indicator (fun w => Mq M x K w) w ∂cgv p|
          ≤ ∫ w, |gsᶜ.indicator (fun w => Mq M x K w) w| ∂cgv p := abs_integral_le_integral_abs
        _ ≤ ∫ w, (Mq M x K w ^ 2 + gsᶜ.indicator (fun _ => (1 : ℝ)) w) / 2 ∂cgv p :=
            integral_mono_of_nonneg (ae_of_all _ (fun w => abs_nonneg _)) hI3 (ae_of_all _ hpt)
        _ = (∫ w, Mq M x K w ^ 2 ∂cgv p + (cgv p).real gsᶜ) / 2 := by
            rw [integral_div, integral_add hI2 ((integrable_const _).indicator hgs.compl),
              integral_indicator_const _ hgs.compl, smul_eq_mul, mul_one]
        _ ≤ (V + J X) / 2 := by rw [hJX]; linarith
    · have h0 : ∀ w : Fin p → ℂ, gs.indicator (fun w => Mq M x K w) w = 0 := by
        intro w
        refine Set.indicator_of_notMem (fun hg => hKe ?_) _
        exact (good_step hM he1 hx hpsdK.isHermitian hpsdK.eigenvalues_nonneg w hg).1
      simp only [h0, integral_zero, abs_zero]
      positivity
  have hJb : ∀ X, |J X| ≤ 1 := fun X => abs_int_le 1 (fun w => ind_one_abs bad _)
  have hIJ : Integrable (fun X => (V + J X) / 2) π :=
    ((integrable_const V).add (iob hJm 1 hJb)).div_const 2
  calc |∫ X, ∫ w, dk x e1 k (Function.update X k w) ∂cgv p ∂π|
      ≤ ∫ X, |∫ w, dk x e1 k (Function.update X k w) ∂cgv p| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫ X, (V + J X) / 2 ∂π :=
        integral_mono_of_nonneg (ae_of_all _ (fun X => abs_nonneg _)) hIJ (ae_of_all _ hin)
    _ = (V + π.real bad) / 2 := by
        rw [integral_div, integral_add (integrable_const V) (iob hJm 1 hJb), hJ, integral_const, probReal_univ,
          one_smul]

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

open Classical in
noncomputable def gI {M p : ℕ} (e1 : ℝ) (X : Fin M → Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then 1 else 0

open Classical in
noncomputable def Hk {M p : ℕ} (x e1 : ℝ) (k : Fin M) (X : Fin M → Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then qk x X k / (1 - qk x X k) else 0

open Classical in
noncomputable def rk {M p : ℕ} (x e1 : ℝ) (k : Fin M) (X : Fin M → Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then
    (M : ℝ)⁻¹ * (resT x (Smat X) - resT x (Smat (Function.update X k 0))) else 0

open Classical in
noncomputable def Ek {M p : ℕ} (x e1 c : ℝ) (k : Fin M) (X : Fin M → Fin p → ℂ) : ℝ :=
  if ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef then qk x X k - c else 0

theorem measurableSet_good {M p : ℕ} (e1 : ℝ) :
    MeasurableSet {X : Fin M → Fin p → ℂ | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef} :=
  ((isClosed_good e1).preimage continuous_Smat).measurableSet

theorem measurable_gI {M p : ℕ} (e1 : ℝ) : Measurable (fun X : Fin M → Fin p → ℂ => gI e1 X) := by
  unfold gI
  exact Measurable.ite (measurableSet_good e1) measurable_const measurable_const

theorem measurable_Hk {M p : ℕ} (x e1 : ℝ) (k : Fin M) :
    Measurable (fun X : Fin M → Fin p → ℂ => Hk x e1 k X) := by
  unfold Hk
  exact Measurable.ite (measurableSet_good e1)
    ((measurable_qk x k).div (measurable_const.sub (measurable_qk x k))) measurable_const

theorem measurable_rk {M p : ℕ} (x e1 : ℝ) (k : Fin M) :
    Measurable (fun X : Fin M → Fin p → ℂ => rk x e1 k X) := by
  unfold rk
  exact Measurable.ite (measurableSet_good e1)
    (((measurable_resT continuous_Smat x).sub (measurable_resT (continuous_Smat_upd k) x)).const_mul _)
    measurable_const

theorem measurable_Ekf {M p : ℕ} (x e1 c : ℝ) (k : Fin M) :
    Measurable (fun X : Fin M → Fin p → ℂ => Ek x e1 c k X) := by
  unfold Ek
  exact Measurable.ite (measurableSet_good e1) ((measurable_qk x k).sub measurable_const) measurable_const

theorem Ff_nonneg {M p : ℕ} {x e1 : ℝ} (hx : e1 < x) (X : Fin M → Fin p → ℂ) : 0 ≤ Ff x e1 X := by
  unfold Ff
  split_ifs with hg
  · have hH := (Smat_psd X).isHermitian
    exact (res_bounds hH hx ((eig_le_iff_posSemidef hH e1).mpr hg)).1
  · exact le_rfl

theorem one_sub_gI {M p : ℕ} (e1 : ℝ) (X : Fin M → Fin p → ℂ) :
    1 - gI e1 X = {X : Fin M → Fin p → ℂ | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
      Smat X).PosSemidef}.indicator (fun _ => (1 : ℝ)) X := by
  unfold gI
  split_ifs with hg
  · rw [Set.indicator_of_notMem (by simpa using hg)]; ring
  · rw [Set.indicator_of_mem (by simpa using hg)]; ring

theorem sum_Hk {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (X : Fin M → Fin p → ℂ) :
    x * Ff x e1 X - p * gI e1 X = ∑ k, Hk x e1 k X := by
  unfold Ff gI Hk
  split_ifs with hg
  · rw [mul_one, selfcons hM he1 hx X hg]
  · simp

theorem rk_bounds {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M)
    (X : Fin M → Fin p → ℂ) :
    0 ≤ rk x e1 k X ∧ rk x e1 k X ≤ (M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x))) := by
  have hMi : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have hb0 : 0 ≤ (x - e1)⁻¹ / ((x - e1) / (2 * x)) := by
    have : 0 < x - e1 := by linarith
    have : 0 < x := by linarith
    positivity
  unfold rk
  split_ifs with hg
  · obtain ⟨_, _, h3, h4⟩ := resT_loo hM he1 hx X hg k
    exact ⟨mul_nonneg hMi h3, mul_le_mul_of_nonneg_left h4 hMi⟩
  · exact ⟨le_rfl, mul_nonneg hMi hb0⟩

theorem Ek_eq {M p : ℕ} (hM : 0 < M) (x e1 c : ℝ) (k : Fin M) (X : Fin M → Fin p → ℂ) :
    Ek x e1 c k X = dk x e1 k X + (Ff x e1 X / M - c) + c * (1 - gI e1 X) - rk x e1 k X := by
  unfold Ek dk Ff gI rk
  split_ifs with hg
  · rw [div_eq_mul_inv]; ring
  · simp

theorem Ek_le {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M)
    (X : Fin M → Fin p → ℂ) : Ek x e1 0 k X ≤ 1 - (x - e1) / (2 * x) := by
  have hk : (x - e1) / (2 * x) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  unfold Ek
  split_ifs with hg
  · rw [sub_zero]; exact (resT_loo hM he1 hx X hg k).2.1
  · linarith

theorem Hk_bound {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M)
    (X : Fin M → Fin p → ℂ) : |Hk x e1 k X| ≤ 1 / ((x - e1) / (2 * x)) := by
  have hκ : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
  unfold Hk
  split_ifs with hg
  · obtain ⟨h1, h2, _, _⟩ := resT_loo hM he1 hx X hg k
    have hpos : 0 < 1 - qk x X k := by linarith
    rw [abs_of_nonneg (div_nonneg h1 hpos.le)]
    rw [div_le_div_iff₀ hpos hκ]
    nlinarith
  · rw [abs_zero]; positivity

theorem taylor_h {q c κ : ℝ} (hκ : 0 < κ) (hq0 : 0 ≤ q) (hq : q ≤ 1 - κ) (hc0 : 0 ≤ c) (hc : c ≤ 1 - κ / 2) :
    |q / (1 - q) - c / (1 - c) - (q - c) / (1 - c) ^ 2| ≤ 4 / κ ^ 3 * (q - c) ^ 2 := by
  have h1 : κ ≤ 1 - q := by linarith
  have h2 : κ / 2 ≤ 1 - c := by linarith
  have hq1 : 0 < 1 - q := by linarith
  have hc1 : 0 < 1 - c := by linarith
  have hid : q / (1 - q) - c / (1 - c) - (q - c) / (1 - c) ^ 2 = (q - c) ^ 2 * ((1 - q) * (1 - c) ^ 2)⁻¹ := by
    field_simp
    ring
  have hD : κ ^ 3 / 4 ≤ (1 - q) * (1 - c) ^ 2 := by
    have h3 : (κ / 2) ^ 2 ≤ (1 - c) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    calc κ ^ 3 / 4 = κ * (κ / 2) ^ 2 := by ring
      _ ≤ (1 - q) * (1 - c) ^ 2 := mul_le_mul h1 h3 (by positivity) hq1.le
  have hinv : ((1 - q) * (1 - c) ^ 2)⁻¹ ≤ 4 / κ ^ 3 := by
    rw [show 4 / κ ^ 3 = (κ ^ 3 / 4)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) hD
  rw [hid, abs_of_nonneg (by positivity), mul_comm (4 / κ ^ 3)]
  exact mul_le_mul_of_nonneg_left hinv (sq_nonneg _)

theorem Hk_rem {M p : ℕ} (hM : 0 < M) {x e1 c : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (hc0 : 0 ≤ c)
    (hc : c ≤ 1 - (x - e1) / (2 * x) / 2) (k : Fin M) (X : Fin M → Fin p → ℂ) :
    |Hk x e1 k X - c / (1 - c) * gI e1 X - Ek x e1 c k X / (1 - c) ^ 2| ≤
      4 / ((x - e1) / (2 * x)) ^ 3 * Ek x e1 c k X ^ 2 := by
  have hκ : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
  unfold Hk gI Ek
  split_ifs with hg
  · obtain ⟨h1, h2, _, _⟩ := resT_loo hM he1 hx X hg k
    rw [mul_one]
    exact taylor_h hκ h1 h2 hc0 hc
  · simp

theorem sq4 (a b c d : ℝ) : (a + b + c - d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a + d), sq_nonneg (b - c), sq_nonneg (b + d),
    sq_nonneg (c + d)]

theorem gI_sq {M p : ℕ} (e1 : ℝ) (X : Fin M → Fin p → ℂ) : (1 - gI e1 X) ^ 2 = 1 - gI e1 X := by
  unfold gI; split_ifs <;> ring

theorem isProb_law (M p : ℕ) : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw M p) := by
  have := Weyl.isProb_cg
  have hν : IsProbabilityMeasure (cgv p) := by unfold cgv; infer_instance
  show IsProbabilityMeasure (Measure.pi fun _ : Fin M => cgv p)
  infer_instance

theorem iob2 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {φ : α → ℝ}
    (hφ : Measurable φ) (C : ℝ) (h : ∀ x, |φ x| ≤ C) : Integrable (fun x => φ x ^ 2) μ :=
  iob (hφ.pow_const 2) (C ^ 2) (fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h x) 2)

theorem int_le_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {φ : α → ℝ}
    (hφ : Integrable φ μ) (C : ℝ) (h : ∀ x, φ x ≤ C) : ∫ x, φ x ∂μ ≤ C := by
  have := integral_mono hφ (integrable_const C) h
  rwa [integral_const, probReal_univ, one_smul] at this

theorem int_one_sub_gI (M p : ℕ) (e1 : ℝ) :
    ∫ X, (1 - gI e1 X) ∂SpikedWishart.SoftEdge.sampleLaw M p = Pbad M p e1 := by
  have hbad : MeasurableSet {X : Fin M → Fin p → ℂ | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
      Smat X).PosSemidef} := (measurableSet_good e1).compl
  rw [integral_congr_ae (ae_of_all _ (fun X => one_sub_gI e1 X)), integral_indicator_const _ hbad,
    smul_eq_mul, mul_one]
  rfl

theorem gI_abs {M p : ℕ} (e1 : ℝ) (X : Fin M → Fin p → ℂ) : |gI e1 X| ≤ 1 := by
  unfold gI; split_ifs <;> simp

theorem int_gI (M p : ℕ) (e1 : ℝ) :
    ∫ X, gI e1 X ∂SpikedWishart.SoftEdge.sampleLaw M p = 1 - Pbad M p e1 := by
  have := isProb_law M p
  have h := int_one_sub_gI M p e1
  rw [integral_sub (integrable_const 1) (iob (measurable_gI e1) 1 (gI_abs e1)), integral_const,
    probReal_univ, one_smul] at h
  linarith

theorem cbar_nonneg {M p : ℕ} {x e1 : ℝ} (hx : e1 < x) : 0 ≤ cbar M p x e1 := by
  unfold cbar
  exact div_nonneg (integral_nonneg (fun X => Ff_nonneg hx X)) (Nat.cast_nonneg M)

theorem int_Ff_div {M p : ℕ} (x e1 : ℝ) :
    ∫ X, Ff x e1 X / M ∂SpikedWishart.SoftEdge.sampleLaw M p = cbar M p x e1 := by
  unfold cbar; rw [integral_div]

theorem int_Ek {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M) :
    |∫ X, Ek x e1 (cbar M p x e1) k X ∂SpikedWishart.SoftEdge.sampleLaw M p| ≤
      (((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) + Pbad M p e1) / 2 + cbar M p x e1 * Pbad M p e1 +
        (M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x))) := by
  have := isProb_law M p
  set c := cbar M p x e1 with hc
  have hI1 : Integrable (fun X => dk x e1 k X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_dk x e1 k) _ (dk_bound hM he1 hx k)
  have hIF : Integrable (fun X => Ff x e1 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_Ff x e1) _ (Ff_bound hx)
  have hI2 : Integrable (fun X => Ff x e1 X / M - c) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    (hIF.div_const _).sub (integrable_const c)
  have hIg : Integrable (fun X => gI e1 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_gI e1) 1 (gI_abs e1)
  have hI3 : Integrable (fun X => c * (1 - gI e1 X)) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    ((integrable_const 1).sub hIg).const_mul c
  have hrb := fun X : Fin M → Fin p → ℂ => rk_bounds hM he1 hx k X
  have hI4 : Integrable (fun X => rk x e1 k X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_rk x e1 k) _ (fun X => by rw [abs_of_nonneg (hrb X).1]; exact (hrb X).2)
  have hA2 : Integrable (fun X => dk x e1 k X + (Ff x e1 X / M - c)) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    hI1.add hI2
  have hA3 : Integrable (fun X => dk x e1 k X + (Ff x e1 X / M - c) + c * (1 - gI e1 X))
    (SpikedWishart.SoftEdge.sampleLaw M p) := hA2.add hI3
  rw [integral_congr_ae (ae_of_all _ (fun X => Ek_eq hM x e1 c k X)),
    integral_sub hA3 hI4, integral_add hA2 hI3, integral_add hI1 hI2,
    integral_sub (hIF.div_const _) (integrable_const c), int_Ff_div, integral_const, probReal_univ, one_smul,
    integral_const_mul, int_one_sub_gI]
  have hr0 : 0 ≤ ∫ X, rk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p :=
    integral_nonneg (fun X => (hrb X).1)
  have hr1 := int_le_of_le hI4 _ (fun X => (hrb X).2)
  have hd := dk_mean hM he1 hx k (p := p)
  have hc0 : 0 ≤ c := cbar_nonneg hx
  have hP0 : 0 ≤ Pbad M p e1 := measureReal_nonneg
  unfold Pbad at hP0 ⊢
  rw [← hc] at *
  have h1 := abs_add_le ((∫ X, dk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p) + (c - c))
    (c * (SpikedWishart.SoftEdge.sampleLaw M p).real
      {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef})
  have h2 := abs_sub (((∫ X, dk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p) + (c - c)) +
    (c * (SpikedWishart.SoftEdge.sampleLaw M p).real
      {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef}))
    (∫ X, rk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p)
  rw [sub_self, add_zero] at h1 h2
  rw [sub_self, add_zero]
  rw [abs_of_nonneg (mul_nonneg hc0 hP0)] at h1
  rw [abs_of_nonneg hr0] at h2
  linarith

theorem int_Ek_sq {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (k : Fin M) :
    ∫ X, Ek x e1 (cbar M p x e1) k X ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p ≤
      4 * (((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) +
        (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) / M + cbar M p x e1 ^ 2 * Pbad M p e1 +
        ((M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x)))) ^ 2) := by
  have := isProb_law M p
  set c := cbar M p x e1 with hc
  set I := ∫ X, Ff x e1 X ∂SpikedWishart.SoftEdge.sampleLaw M p with hI
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hcI : c = I / M := rfl
  have hIb : |I| ≤ p * (x - e1)⁻¹ := abs_int_le _ (Ff_bound hx)
  have hrb := fun X : Fin M → Fin p → ℂ => rk_bounds hM he1 hx k X
  have hJ1 : Integrable (fun X => dk x e1 k X ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob2 (measurable_dk x e1 k) _ (dk_bound hM he1 hx k)
  have hV0 : Integrable (fun X => (Ff x e1 X - I) ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (((measurable_Ff x e1).sub measurable_const).pow_const 2) _
      (fun X => sq_sub_bound (Ff_bound hx X) hIb)
  have hJ2 : Integrable (fun X => (Ff x e1 X / M - c) ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) := by
    refine (hV0.div_const ((M : ℝ) ^ 2)).congr (ae_of_all _ (fun X => ?_))
    beta_reduce; rw [hcI, div_sub_div_same, div_pow]
  have hIg : Integrable (fun X => gI e1 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_gI e1) 1 (gI_abs e1)
  have hJ3 : Integrable (fun X => (c * (1 - gI e1 X)) ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) := by
    have h1g : Integrable (fun X => 1 - gI e1 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
      (integrable_const 1).sub hIg
    exact (h1g.const_mul (c ^ 2)).congr (ae_of_all _ (fun X => by beta_reduce; rw [mul_pow, gI_sq]))
  have hJ4 : Integrable (fun X => rk x e1 k X ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob2 (measurable_rk x e1 k) _ (fun X => by rw [abs_of_nonneg (hrb X).1]; exact (hrb X).2)
  have hpt : ∀ X : Fin M → Fin p → ℂ, Ek x e1 c k X ^ 2 ≤ 4 * (dk x e1 k X ^ 2 + (Ff x e1 X / M - c) ^ 2 +
      (c * (1 - gI e1 X)) ^ 2 + rk x e1 k X ^ 2) := by
    intro X; rw [Ek_eq hM]; exact sq4 _ _ _ _
  have hK2 : Integrable (fun X => dk x e1 k X ^ 2 + (Ff x e1 X / M - c) ^ 2)
    (SpikedWishart.SoftEdge.sampleLaw M p) := hJ1.add hJ2
  have hK3 : Integrable (fun X => dk x e1 k X ^ 2 + (Ff x e1 X / M - c) ^ 2 + (c * (1 - gI e1 X)) ^ 2)
    (SpikedWishart.SoftEdge.sampleLaw M p) := hK2.add hJ3
  have hK4 : Integrable (fun X => dk x e1 k X ^ 2 + (Ff x e1 X / M - c) ^ 2 + (c * (1 - gI e1 X)) ^ 2 +
    rk x e1 k X ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) := hK3.add hJ4
  have hJ : Integrable (fun X => 4 * (dk x e1 k X ^ 2 + (Ff x e1 X / M - c) ^ 2 + (c * (1 - gI e1 X)) ^ 2 +
    rk x e1 k X ^ 2)) (SpikedWishart.SoftEdge.sampleLaw M p) := hK4.const_mul 4
  have hE : Integrable (fun X => Ek x e1 c k X ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    hJ.mono' ((measurable_Ekf x e1 c k).pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun X => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt X))
  refine (integral_mono hE hJ hpt).trans ?_
  rw [integral_const_mul, integral_add hK3 hJ4, integral_add hK2 hJ3, integral_add hJ1 hJ2]
  have ha := dk_sq hM he1 hx k (p := p)
  have hb : ∫ X, (Ff x e1 X / M - c) ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p =
      (∫ X, (Ff x e1 X - I) ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p) / (M : ℝ) ^ 2 := by
    rw [← integral_div]
    refine integral_congr_ae (ae_of_all _ (fun X => ?_))
    beta_reduce; rw [hcI, div_sub_div_same, div_pow]
  have hvar := var_Ff hM he1 hx (p := p)
  rw [← hI] at hvar
  have hb2 : (∫ X, (Ff x e1 X - I) ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p) / (M : ℝ) ^ 2 ≤
      (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pbad M p e1) / M := by
    unfold Pbad
    rw [div_le_div_iff₀ (by positivity) hMp]
    calc (∫ X, (Ff x e1 X - I) ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p) * M
        ≤ (M * (condC p M x e1 + bnd0 p M x e1 ^ 2 * (SpikedWishart.SoftEdge.sampleLaw M p).real
        {X | ¬ ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Smat X).PosSemidef})) * M :=
          mul_le_mul_of_nonneg_right hvar hMp.le
      _ = _ := by ring
  have hc3 : ∫ X, (c * (1 - gI e1 X)) ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p = c ^ 2 * Pbad M p e1 := by
    rw [← int_one_sub_gI M p e1, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (fun X => by beta_reduce; rw [mul_pow, gI_sq]))
  have hd4 := int_le_of_le hJ4 (((M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x)))) ^ 2)
    (fun X => pow_le_pow_left₀ (hrb X).1 (hrb X).2 2)
  rw [hb, hc3]
  linarith

theorem Ek_abs {M p : ℕ} (hM : 0 < M) {x e1 c : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (hc0 : 0 ≤ c) (k : Fin M)
    (X : Fin M → Fin p → ℂ) : |Ek x e1 c k X| ≤ 1 + c := by
  have hκ : 0 < (x - e1) / (2 * x) := div_pos (by linarith) (by linarith)
  unfold Ek
  split_ifs with hg
  · obtain ⟨h1, h2, _, _⟩ := resT_loo hM he1 hx X hg k
    rw [abs_le]; constructor <;> linarith
  · rw [abs_zero]; linarith

theorem int_Hk {M p : ℕ} (hM : 0 < M) {x e1 c : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) (hc0 : 0 ≤ c)
    (hc : c ≤ 1 - (x - e1) / (2 * x) / 2) (k : Fin M) :
    |∫ X, Hk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p - c / (1 - c) * (1 - Pbad M p e1) -
        (∫ X, Ek x e1 c k X ∂SpikedWishart.SoftEdge.sampleLaw M p) / (1 - c) ^ 2| ≤
      4 / ((x - e1) / (2 * x)) ^ 3 * ∫ X, Ek x e1 c k X ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p := by
  have := isProb_law M p
  have hH : Integrable (fun X => Hk x e1 k X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_Hk x e1 k) _ (Hk_bound hM he1 hx k)
  have hG : Integrable (fun X => c / (1 - c) * gI e1 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    (iob (measurable_gI e1) 1 (gI_abs e1)).const_mul _
  have hE : Integrable (fun X => Ek x e1 c k X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_Ekf x e1 c k) _ (Ek_abs hM he1 hx hc0 k)
  have hE' : Integrable (fun X => Ek x e1 c k X / (1 - c) ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    hE.div_const _
  have hE2 : Integrable (fun X => Ek x e1 c k X ^ 2) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob2 (measurable_Ekf x e1 c k) _ (Ek_abs hM he1 hx hc0 k)
  have hHG : Integrable (fun X => Hk x e1 k X - c / (1 - c) * gI e1 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    hH.sub hG
  have heq : ∫ X, (Hk x e1 k X - c / (1 - c) * gI e1 X - Ek x e1 c k X / (1 - c) ^ 2)
      ∂SpikedWishart.SoftEdge.sampleLaw M p =
      ∫ X, Hk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p - c / (1 - c) * (1 - Pbad M p e1) -
        (∫ X, Ek x e1 c k X ∂SpikedWishart.SoftEdge.sampleLaw M p) / (1 - c) ^ 2 := by
    rw [integral_sub hHG hE', integral_sub hH hG, integral_const_mul, int_gI, integral_div]
  rw [← heq, ← integral_const_mul]
  refine abs_integral_le_integral_abs.trans ?_
  exact integral_mono_of_nonneg (ae_of_all _ (fun X => abs_nonneg _)) (hE2.const_mul _)
    (ae_of_all _ (fun X => Hk_rem hM he1 hx hc0 hc k X))

theorem int_sum_Hk {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x) :
    x * M * cbar M p x e1 - p * (1 - Pbad M p e1) =
      ∑ k, ∫ X, Hk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p := by
  have := isProb_law M p
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hIF : Integrable (fun X => x * Ff x e1 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    (iob (measurable_Ff x e1) _ (Ff_bound hx)).const_mul x
  have hIg : Integrable (fun X => (p : ℝ) * gI e1 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    (iob (measurable_gI e1) 1 (gI_abs e1)).const_mul _
  rw [← integral_finset_sum _ (fun k _ => iob (measurable_Hk x e1 k) _ (Hk_bound hM he1 hx k))]
  rw [← integral_congr_ae (ae_of_all _ (fun X => sum_Hk hM he1 hx X)), integral_sub hIF hIg,
    integral_const_mul, integral_const_mul, int_gI]
  unfold cbar
  field_simp

theorem bias {M p : ℕ} (hM : 0 < M) {x e1 : ℝ} (he1 : 0 ≤ e1) (hx : e1 < x)
    (hsmall : (((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) + Pbad M p e1) / 2 +
      (M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x))) ≤ (x - e1) / (2 * x) / 2) :
    0 ≤ cbar M p x e1 ∧ cbar M p x e1 ≤ 1 - (x - e1) / (2 * x) / 2 ∧
      |x * cbar M p x e1 - p / M - cbar M p x e1 / (1 - cbar M p x e1)| ≤ biasErr p M x e1 (Pbad M p e1) := by
  have := isProb_law M p
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hxe : 0 < x - e1 := by linarith
  have hκ : 0 < (x - e1) / (2 * x) := div_pos hxe (by linarith)
  have hκ1 : (x - e1) / (2 * x) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hP0 : 0 ≤ Pbad M p e1 := by unfold Pbad; exact measureReal_nonneg
  have hV0 : 0 ≤ ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) := by positivity
  have hr0 : 0 ≤ (M : ℝ)⁻¹ * ((x - e1)⁻¹ / ((x - e1) / (2 * x))) :=
    mul_nonneg (inv_nonneg.mpr hMp.le) (div_nonneg (inv_nonneg.mpr hxe.le) hκ.le)
  have hc0 : 0 ≤ cbar M p x e1 := cbar_nonneg hx
  -- upper bound on c
  set k0 : Fin M := ⟨0, hM⟩
  have hIF : Integrable (fun X => Ff x e1 X / M) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    (iob (measurable_Ff x e1) _ (Ff_bound hx)).div_const _
  have hId : Integrable (fun X => dk x e1 k0 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_dk x e1 k0) _ (dk_bound hM he1 hx k0)
  have hrb := fun X : Fin M → Fin p → ℂ => rk_bounds hM he1 hx k0 X
  have hIr : Integrable (fun X => rk x e1 k0 X) (SpikedWishart.SoftEdge.sampleLaw M p) :=
    iob (measurable_rk x e1 k0) _ (fun X => by rw [abs_of_nonneg (hrb X).1]; exact (hrb X).2)
  have hI3 : Integrable (fun X => (1 - (x - e1) / (2 * x)) - dk x e1 k0 X)
    (SpikedWishart.SoftEdge.sampleLaw M p) := (integrable_const _).sub hId
  have hpt : ∀ X : Fin M → Fin p → ℂ, Ff x e1 X / M ≤ (1 - (x - e1) / (2 * x)) - dk x e1 k0 X + rk x e1 k0 X := by
    intro X
    have h1 := Ek_eq hM x e1 0 k0 X
    have h2 := Ek_le hM he1 hx k0 X
    rw [h1] at h2
    linarith
  have hI4 : Integrable (fun X => (1 - (x - e1) / (2 * x)) - dk x e1 k0 X + rk x e1 k0 X)
    (SpikedWishart.SoftEdge.sampleLaw M p) := hI3.add hIr
  have hcup := integral_mono hIF hI4 hpt
  rw [int_Ff_div, integral_add hI3 hIr, integral_sub (integrable_const _) hId, integral_const, probReal_univ,
    one_smul] at hcup
  have hd : |∫ X, dk x e1 k0 X ∂SpikedWishart.SoftEdge.sampleLaw M p| ≤
      (((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) + Pbad M p e1) / 2 := dk_mean hM he1 hx k0
  have hr1 := int_le_of_le hIr _ (fun X => (hrb X).2)
  have hdl := neg_abs_le (∫ X, dk x e1 k0 X ∂SpikedWishart.SoftEdge.sampleLaw M p)
  have hc1 : cbar M p x e1 ≤ 1 - (x - e1) / (2 * x) / 2 := by linarith
  refine ⟨hc0, hc1, ?_⟩
  -- per-k bound
  set c := cbar M p x e1 with hc
  set κ := (x - e1) / (2 * x) with hκdef
  set V := ((M : ℝ)⁻¹) ^ 2 * (p * ((x - e1)⁻¹) ^ 2) with hV
  set r := (M : ℝ)⁻¹ * ((x - e1)⁻¹ / κ) with hr
  set Pb := Pbad M p e1 with hPb
  set A1 := (V + Pb) / 2 + Pb + r with hA1
  set A2 := 4 * (V + (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pb) / M + Pb + r ^ 2) with hA2
  set B := 4 / κ ^ 2 * A1 + 4 / κ ^ 3 * A2 with hB
  have hc1' : 1 - c > 0 := by linarith
  have hcle1 : c ≤ 1 := by linarith
  have hk2 : κ / 2 ≤ 1 - c := by linarith
  have hsq : κ ^ 2 / 4 ≤ (1 - c) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ κ / 2) hk2 2
    rw [div_pow] at this; norm_num at this ⊢; linarith
  have hinv : 1 / (1 - c) ^ 2 ≤ 4 / κ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hA10 : 0 ≤ A1 := by positivity
  have hcP : c * Pb ≤ Pb := by
    have := mul_le_mul_of_nonneg_right hcle1 hP0; rwa [one_mul] at this
  have hc2P : c ^ 2 * Pb ≤ Pb := by
    have := mul_le_mul_of_nonneg_right (pow_le_one₀ hc0 hcle1 : c ^ 2 ≤ 1) hP0; rwa [one_mul] at this
  have hkey : ∀ k : Fin M, |∫ X, Hk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p - c / (1 - c) * (1 - Pb)| ≤ B := by
    intro k
    have h1 : |∫ X, Hk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p - c / (1 - c) * (1 - Pb) -
        (∫ X, Ek x e1 c k X ∂SpikedWishart.SoftEdge.sampleLaw M p) / (1 - c) ^ 2| ≤
        4 / κ ^ 3 * ∫ X, Ek x e1 c k X ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p :=
      int_Hk hM he1 hx hc0 hc1 k (p := p)
    have h2 : |∫ X, Ek x e1 c k X ∂SpikedWishart.SoftEdge.sampleLaw M p| ≤ (V + Pb) / 2 + c * Pb + r :=
      int_Ek hM he1 hx k (p := p)
    have h3 : ∫ X, Ek x e1 c k X ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p ≤
        4 * (V + (condC p M x e1 + bnd0 p M x e1 ^ 2 * Pb) / M + c ^ 2 * Pb + r ^ 2) :=
      int_Ek_sq hM he1 hx k (p := p)
    have h4 : |(∫ X, Ek x e1 c k X ∂SpikedWishart.SoftEdge.sampleLaw M p) / (1 - c) ^ 2| ≤ 4 / κ ^ 2 * A1 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 - c) ^ 2), div_eq_mul_one_div]
      calc |∫ X, Ek x e1 c k X ∂SpikedWishart.SoftEdge.sampleLaw M p| * (1 / (1 - c) ^ 2)
          ≤ A1 * (4 / κ ^ 2) := mul_le_mul (by linarith) hinv (by positivity) hA10
        _ = 4 / κ ^ 2 * A1 := by ring
    have h5 : 4 / κ ^ 3 * ∫ X, Ek x e1 c k X ^ 2 ∂SpikedWishart.SoftEdge.sampleLaw M p ≤ 4 / κ ^ 3 * A2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h6 := abs_add_le (∫ X, Hk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p - c / (1 - c) * (1 - Pb) -
        (∫ X, Ek x e1 c k X ∂SpikedWishart.SoftEdge.sampleLaw M p) / (1 - c) ^ 2)
      ((∫ X, Ek x e1 c k X ∂SpikedWishart.SoftEdge.sampleLaw M p) / (1 - c) ^ 2)
    rw [sub_add_cancel] at h6
    linarith
  have hsum : x * M * c - p * (1 - Pb) = ∑ k, ∫ X, Hk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p :=
    int_sum_Hk hM he1 hx (p := p)
  have hS : x * M * c - p * (1 - Pb) - M * (c / (1 - c) * (1 - Pb)) =
      ∑ k : Fin M, (∫ X, Hk x e1 k X ∂SpikedWishart.SoftEdge.sampleLaw M p - c / (1 - c) * (1 - Pb)) := by
    rw [Finset.sum_sub_distrib, ← hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hSb : |x * M * c - p * (1 - Pb) - M * (c / (1 - c) * (1 - Pb))| ≤ M * B := by
    rw [hS]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun k _ => hkey k)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hM1 : x * M * c - p * (1 - Pb) - M * (c / (1 - c) * (1 - Pb)) =
      M * (x * c - p / M * (1 - Pb) - c / (1 - c) * (1 - Pb)) := by
    field_simp
  rw [hM1, abs_mul, abs_of_pos hMp] at hSb
  have hT : |x * c - p / M * (1 - Pb) - c / (1 - c) * (1 - Pb)| ≤ B := le_of_mul_le_mul_left hSb hMp
  have hh : c / (1 - c) ≤ 2 / κ := by
    rw [div_le_div_iff₀ hc1' hκ]
    have := mul_le_of_le_one_left hκ.le hcle1
    linarith
  have hh0 : 0 ≤ c / (1 - c) := div_nonneg hc0 hc1'.le
  have hpM : 0 ≤ (p : ℝ) / M := div_nonneg (Nat.cast_nonneg p) hMp.le
  have hU := abs_sub (x * c - p / M * (1 - Pb) - c / (1 - c) * (1 - Pb)) ((p / M + c / (1 - c)) * Pb)
  rw [abs_of_nonneg (mul_nonneg (add_nonneg hpM hh0) hP0)] at hU
  have hE : biasErr p M x e1 Pb = B + (p / M + 2 / κ) * Pb := rfl
  have hW : (p / M + c / (1 - c)) * Pb ≤ (p / M + 2 / κ) * Pb := mul_le_mul_of_nonneg_right (by linarith) hP0
  rw [hE]
  have hid : x * c - p / M - c / (1 - c) =
      x * c - p / M * (1 - Pb) - c / (1 - c) * (1 - Pb) - (p / M + c / (1 - c)) * Pb := by ring
  rw [hid]
  linarith

end Q2

end

-- ===== from QM.lean =====
section

namespace Q2

theorem q2_moments : Q2_moments := by
  intro M p hM x e1 he1 hx
  exact ⟨var_Ff hM he1 hx, fun h => bias hM he1 hx h⟩

end Q2

end

end SpikedWishart.Separated.Lib

open SpikedWishart.Separated in
theorem solution :
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
        ((p : ℝ) / M + 2 / κ) * Pb) := by
  exact SpikedWishart.Separated.Lib.Q2.q2_moments
