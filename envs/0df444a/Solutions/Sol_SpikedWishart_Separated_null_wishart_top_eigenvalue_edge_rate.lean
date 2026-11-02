-- Prove2me | solution 1 for SpikedWishart.Separated.null_wishart_top_eigenvalue_edge_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:01:28.163987+00:00
-- url     : https://prove2.me/submissions/dff52e4f-ee00-433d-bf86-0add129477b0

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

/-- E (edge bound with polynomial rate; Bai-Silverstein 2004 (1.9a), for Gaussian entries also
Davidson-Szarek 2001 Thm II.13): for `N n ≤ M n`, `M n → ∞` and every power `l`,
`M^l · P(λmax((1/M) G Gᴴ) > (1 + √(N/M))² + ε) → 0`. -/
def P2_edgeRate : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (l : ℕ) (M N : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, N n ≤ M n) →
    Tendsto (fun n => (M n : ℝ) ^ l * (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X})
      atTop (𝓝 0)

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

theorem re_star_self (x : Fin k → ℂ) : (star x ⬝ᵥ x).re = ∑ i, Complex.normSq (x i) := by
  simp [dotProduct, Complex.normSq_apply, Complex.mul_re]

end

-- ===== from Misc.lean =====
section

/-- `re ⟨v, (a - Yᴴ Y) v⟩ = a |v|² - |Y v|²`. -/
theorem re_quad_sub_gram {p M : ℕ} (Y : Matrix (Fin p) (Fin M) ℂ) (a : ℝ) (v : Fin M → ℂ) :
    (star v ⬝ᵥ (((a : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) - Yᴴ * Y) *ᵥ v)).re =
      a * ∑ i, Complex.normSq (v i) - ∑ i, Complex.normSq ((Y *ᵥ v) i) := by
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, smul_mulVec, one_mulVec, dotProduct_smul,
    ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, smul_eq_mul, Complex.re_ofReal_mul,
    re_star_self, re_star_self]

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

theorem nsq_succ {n : ℕ} (v : Fin (n + 1) → ℂ) :
    nsq v = Complex.normSq (v 0) + nsq (Fin.tail v) := by
  simp [nsq, Fin.sum_univ_succ, Fin.tail]

theorem nsq_unitary {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (v : n → ℂ) : nsq (U *ᵥ v) = nsq v := by
  rw [nsq_eq_re, nsq_eq_re, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    ← star_eq_conjTranspose, (mem_unitaryGroup_iff'.mp hU), one_mulVec]

theorem transpose_mem_unitary {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) : Uᵀ ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff]
  have h2 : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have : star Uᵀ = (star U)ᵀ := by ext i j; simp [star_eq_conjTranspose]
  rw [this, ← transpose_mul, h2, transpose_one]

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

theorem Dec.bnd {M N : ℕ} {G : Matrix (Fin M) (Fin N) ℂ} {α β : ℝ} (h : Dec G α β)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : Bnd G (α + β) := by
  obtain ⟨A, C, rfl, hA, hC, -⟩ := h
  exact Bnd.add hα hβ hA hC

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

/-- Block-diagonal `diag(1, V)`. -/
def blk1 {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (Fin.cases (motive := fun _ => ℂ) 1 (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => ℂ) 0 (fun j' => V i' j') j) i

theorem blk1_mul {n : ℕ} (V V' : Matrix (Fin n) (Fin n) ℂ) : blk1 V * blk1 V' = blk1 (V * V') := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [blk1, mul_apply, Fin.sum_univ_succ]

theorem blk1_star {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) : star (blk1 V) = blk1 (star V) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [blk1, star_eq_conjTranspose]

theorem blk1_one {n : ℕ} : blk1 (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [blk1, one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem blk1_mem {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ) :
    blk1 V ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  rw [mem_unitaryGroup_iff, blk1_star, blk1_mul, (mem_unitaryGroup_iff.mp hV), blk1_one]

theorem blk1_col0 {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    ∀ k j : Fin (n + 1), (j : ℕ) = 0 → (k : ℕ) ≠ 0 → blk1 V k j = 0 := by
  intro k j hj hk
  have hj' : j = 0 := Fin.ext hj
  subst hj'
  cases k using Fin.cases with
  | zero => exact absurd rfl hk
  | succ k => simp [blk1]

/-- The bidiagonal step shape `[[a, b e₀ᵀ], [0, Y]]`. -/
def Kblk {M N : ℕ} (a b : ℂ) (Y : Matrix (Fin M) (Fin N) ℂ) : Matrix (Fin (M + 1)) (Fin (N + 1)) ℂ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ)
    (Fin.cases (motive := fun _ => ℂ) a (fun j' => if (j' : ℕ) = 0 then b else 0) j)
    (fun i' => Fin.cases (motive := fun _ => ℂ) 0 (fun j' => Y i' j') j) i

theorem Dec_Kblk {M N : ℕ} {a b : ℂ} {α β : ℝ} (haα : ‖a‖ ≤ α) (hbβ : ‖b‖ ≤ β)
    {Y : Matrix (Fin M) (Fin N) ℂ} (hY : Dec Y α β) : Dec (Kblk a b Y) α β := by
  obtain ⟨A, C, rfl, hA, hC, h0⟩ := hY
  let A' : Matrix (Fin (M + 1)) (Fin (N + 1)) ℂ := Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ)
    (Fin.cases (motive := fun _ => ℂ) a (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => ℂ) 0 (fun j' => A i' j') j) i
  let C' : Matrix (Fin (M + 1)) (Fin (N + 1)) ℂ := Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ)
    (Fin.cases (motive := fun _ => ℂ) 0 (fun j' => if (j' : ℕ) = 0 then b else 0) j)
    (fun i' => Fin.cases (motive := fun _ => ℂ) 0 (fun j' => C i' j') j) i
  have ha2 : Complex.normSq a ≤ α ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) haα 2
  have hb2 : Complex.normSq b ≤ β ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hbβ 2
  refine ⟨A', C', ?_, ?_, ?_, ?_⟩
  · ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [Kblk, A', C']
  · intro v
    have h0 : (A' *ᵥ v) 0 = a * v 0 := by
      simp [A', mulVec, dotProduct, Fin.sum_univ_succ]
    have hs : Fin.tail (A' *ᵥ v) = A *ᵥ Fin.tail v := by
      ext i; simp [A', mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail]
    rw [nsq_succ, h0, hs, nsq_succ v, Complex.normSq_mul]
    have := hA (Fin.tail v)
    have hv0 := Complex.normSq_nonneg (v 0)
    have : Complex.normSq a * Complex.normSq (v 0) ≤ α ^ 2 * Complex.normSq (v 0) :=
      mul_le_mul_of_nonneg_right ha2 hv0
    nlinarith
  · intro v
    cases N with
    | zero =>
      have hz : C' *ᵥ v = 0 := by
        ext i; cases i using Fin.cases <;> simp [C', mulVec, dotProduct, Fin.sum_univ_succ]
      rw [hz]
      have : nsq (0 : Fin (M + 1) → ℂ) = 0 := by simp [nsq]
      rw [this]; exact mul_nonneg (sq_nonneg _) (nsq_nonneg _)
    | succ n =>
      have hc0 : (C' *ᵥ v) 0 = b * v 1 := by
        simp [C', mulVec, dotProduct, Fin.sum_univ_succ]
      have hs : Fin.tail (C' *ᵥ v) = C *ᵥ Fin.cons 0 (Fin.tail (Fin.tail v)) := by
        ext i
        simp [C', mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail, h0 i 0 rfl]
      rw [nsq_succ, hc0, hs, Complex.normSq_mul]
      have h1 := hC (Fin.cons 0 (Fin.tail (Fin.tail v)))
      have hc : nsq (Fin.cons 0 (Fin.tail (Fin.tail v)) : Fin (n + 1) → ℂ) = nsq (Fin.tail (Fin.tail v)) := by
        rw [nsq_succ]; simp
      rw [hc] at h1
      have hv : nsq v = Complex.normSq (v 0) + (Complex.normSq (v 1) + nsq (Fin.tail (Fin.tail v))) := by
        rw [nsq_succ v, nsq_succ (Fin.tail v)]; rfl
      rw [hv]
      have hv0 := Complex.normSq_nonneg (v 0)
      have hv1 := Complex.normSq_nonneg (v 1)
      have : Complex.normSq b * Complex.normSq (v 1) ≤ β ^ 2 * Complex.normSq (v 1) :=
        mul_le_mul_of_nonneg_right hb2 hv1
      have hβ0 : 0 ≤ β ^ 2 * Complex.normSq (v 0) := mul_nonneg (sq_nonneg _) hv0
      nlinarith
  · intro i j hj
    have hj' : j = 0 := Fin.ext hj
    subst hj'
    cases i using Fin.cases <;> simp [C']

end

-- ===== from Q1b.lean =====
section

/-! Q1, Householder reflection: a measurable unitary `rot v` with `rot v *ᵥ v = z • e₀`, `‖z‖ = ‖v‖`. -/

/-- First basis vector. -/
def e0v (m : ℕ) : Fin (m + 1) → ℂ := fun i => if (i : ℕ) = 0 then 1 else 0

/-- Phase of a complex number (`1` at `0`). -/
noncomputable def phs (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem normSq_phs (z : ℂ) : Complex.normSq (phs z) = 1 := by
  unfold phs
  split_ifs with h
  · simp
  · have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    field_simp

theorem conj_phs_mul (z : ℂ) : (starRingEnd ℂ) (phs z) * z = (‖z‖ : ℂ) := by
  unfold phs
  split_ifs with h
  · simp [h]
  · have h1 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have h2 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast h1
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    field_simp
    push_cast; ring

/-- Householder matrix `1 - (2/‖w‖²) w wᴴ`. -/
noncomputable def hh {n : Type*} [Fintype n] [DecidableEq n] (w : n → ℂ) : Matrix n n ℂ :=
  1 - (((2 / nsq w : ℝ)) : ℂ) • vecMulVec w (star w)

theorem star_dot_self {n : Type*} [Fintype n] (w : n → ℂ) : star w ⬝ᵥ w = (nsq w : ℂ) := by
  simp only [dotProduct, nsq, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.normSq_eq_conj_mul_self]

theorem vecMulVec_mulVec' {n : Type*} [Fintype n] (w x u : n → ℂ) :
    vecMulVec w x *ᵥ u = (x ⬝ᵥ u) • w := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem vecMulVec_mul_self {n : Type*} [Fintype n] (w : n → ℂ) :
    vecMulVec w (star w) * vecMulVec w (star w) = (nsq w : ℂ) • vecMulVec w (star w) := by
  ext i j
  rw [mul_apply, Matrix.smul_apply, smul_eq_mul, ← star_dot_self, dotProduct, Finset.sum_mul]
  simp only [vecMulVec_apply, Pi.star_apply]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem nsq_pos {n : Type*} [Fintype n] {w : n → ℂ} (hw : w ≠ 0) : 0 < nsq w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h; push_neg at h; exact hw (funext h)
  have : Complex.normSq (w i) ≤ nsq w :=
    Finset.single_le_sum (f := fun i => Complex.normSq (w i)) (fun j _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  have : 0 < Complex.normSq (w i) := Complex.normSq_pos.mpr hi
  linarith

theorem hh_mem {n : Type*} [Fintype n] [DecidableEq n] {w : n → ℂ} (hw : w ≠ 0) :
    hh w ∈ unitaryGroup n ℂ := by
  have hpos := nsq_pos hw
  have hstar : star (hh w) = hh w := by
    unfold hh
    rw [star_sub, star_one, star_smul, star_eq_conjTranspose (vecMulVec w (star w)),
      conjTranspose_vecMulVec, star_star]
    simp
  rw [mem_unitaryGroup_iff, hstar]
  unfold hh
  set c : ℂ := (((2 / nsq w : ℝ)) : ℂ)
  set P := vecMulVec w (star w)
  have hc : c * c * (nsq w : ℂ) = 2 * c := by
    simp only [c]; push_cast
    have : (nsq w : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
  calc (1 - c • P) * (1 - c • P) = 1 - (2 * c) • P + (c * c) • (P * P) := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
        module
    _ = 1 - (2 * c) • P + (c * c * (nsq w : ℂ)) • P := by
        rw [vecMulVec_mul_self, smul_smul]
    _ = 1 := by rw [hc]; abel

theorem hh_mulVec {n : Type*} [Fintype n] [DecidableEq n] (w v : n → ℂ) :
    hh w *ᵥ v = v - ((((2 / nsq w : ℝ)) : ℂ) * (star w ⬝ᵥ v)) • w := by
  unfold hh
  rw [sub_mulVec, one_mulVec]
  congr 1
  have : ((((2 / nsq w : ℝ)) : ℂ) • vecMulVec w (star w)) *ᵥ v =
      (((2 / nsq w : ℝ)) : ℂ) • (vecMulVec w (star w) *ᵥ v) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this, vecMulVec_mulVec', smul_smul]

/-- Householder target coefficient `z = -‖v‖ · phase(v₀)`. -/
noncomputable def rz {m : ℕ} (v : Fin (m + 1) → ℂ) : ℂ := -((Real.sqrt (nsq v) : ℝ) : ℂ) * phs (v 0)

theorem norm_rz {m : ℕ} (v : Fin (m + 1) → ℂ) : ‖rz v‖ = Real.sqrt (nsq v) := by
  unfold rz
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have : ‖phs (v 0)‖ = 1 := by
    have h := normSq_phs (v 0)
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (phs (v 0))]
  rw [this, mul_one]

noncomputable def rot {m : ℕ} (v : Fin (m + 1) → ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  if v = 0 then 1 else hh (v - rz v • e0v m)

/-- Key computations for `w = v - z e₀`. -/
theorem rot_aux {m : ℕ} (v : Fin (m + 1) → ℂ) :
    star (v - rz v • e0v m) ⬝ᵥ v =
        ((nsq v + Real.sqrt (nsq v) * ‖v 0‖ : ℝ) : ℂ) ∧
      nsq (v - rz v • e0v m) = 2 * (nsq v + Real.sqrt (nsq v) * ‖v 0‖) := by
  set s := Real.sqrt (nsq v)
  have hs2 : s ^ 2 = nsq v := Real.sq_sqrt (nsq_nonneg v)
  have hsplit := nsq_succ v
  set t := nsq (Fin.tail v)
  have hφ := conj_phs_mul (v 0)
  have hφ2 := normSq_phs (v 0)
  have hw0 : (v - rz v • e0v m) 0 = v 0 + (s : ℂ) * phs (v 0) := by
    simp [e0v, rz, s]
  have hws : ∀ i : Fin m, (v - rz v • e0v m) i.succ = v i.succ := by
    intro i; simp [e0v]
  have hn0 : Complex.normSq (v 0) = ‖v 0‖ ^ 2 := Complex.normSq_eq_norm_sq _
  constructor
  · rw [dotProduct, Fin.sum_univ_succ]
    simp only [Pi.star_apply, hw0, hws]
    have h1 : ∑ i : Fin m, star (v i.succ) * v i.succ = (t : ℂ) := by
      simp only [t, nsq, Fin.tail, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [RCLike.star_def, Complex.normSq_eq_conj_mul_self]
    rw [h1, star_add, add_mul, star_mul']
    simp only [RCLike.star_def]
    rw [Complex.conj_ofReal, mul_assoc, hφ, ← Complex.normSq_eq_conj_mul_self, hsplit, hn0]
    push_cast; ring
  · rw [nsq_succ, hw0]
    have htail : Fin.tail (v - rz v • e0v m) = Fin.tail v := by
      ext i; simp [Fin.tail, e0v]
    rw [htail]
    have hexp : Complex.normSq (v 0 + (s : ℂ) * phs (v 0)) =
        Complex.normSq (v 0) + s ^ 2 * Complex.normSq (phs (v 0)) +
          2 * s * ((starRingEnd ℂ) (phs (v 0)) * v 0).re := by
      rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
      have : (v 0 * (starRingEnd ℂ) ((s : ℂ) * phs (v 0))).re =
          s * ((starRingEnd ℂ) (phs (v 0)) * v 0).re := by
        rw [map_mul, Complex.conj_ofReal]
        rw [show v 0 * ((s : ℂ) * (starRingEnd ℂ) (phs (v 0))) =
          (s : ℂ) * ((starRingEnd ℂ) (phs (v 0)) * v 0) by ring, Complex.re_ofReal_mul]
      rw [this]; ring
    rw [hexp, hφ, hφ2, Complex.ofReal_re, hn0]
    have : nsq v = ‖v 0‖ ^ 2 + t := by rw [hsplit, hn0]
    rw [this] at hs2 ⊢
    nlinarith

theorem rot_mem {m : ℕ} (v : Fin (m + 1) → ℂ) : rot v ∈ unitaryGroup (Fin (m + 1)) ℂ := by
  unfold rot
  split_ifs with hv
  · exact one_mem _
  · apply hh_mem
    intro hw
    have h2 := (rot_aux v).2
    rw [hw] at h2
    have h0 : nsq (0 : Fin (m + 1) → ℂ) = 0 := by simp [nsq]
    rw [h0] at h2
    have := nsq_pos hv
    have : 0 ≤ Real.sqrt (nsq v) * ‖v 0‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    linarith

theorem rot_mulVec {m : ℕ} (v : Fin (m + 1) → ℂ) : rot v *ᵥ v = rz v • e0v m := by
  unfold rot
  split_ifs with hv
  · subst hv
    have : rz (0 : Fin (m + 1) → ℂ) = 0 := by simp [rz, nsq]
    rw [this, zero_smul, one_mulVec]
  · rw [hh_mulVec, (rot_aux v).1, (rot_aux v).2]
    have hpos := nsq_pos hv
    have : 0 ≤ Real.sqrt (nsq v) * ‖v 0‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hq : (((2 / (2 * (nsq v + Real.sqrt (nsq v) * ‖v 0‖)) : ℝ)) : ℂ) *
        ((nsq v + Real.sqrt (nsq v) * ‖v 0‖ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      have : nsq v + Real.sqrt (nsq v) * ‖v 0‖ ≠ 0 := by linarith
      field_simp
      simp
    rw [hq, one_smul, sub_sub_cancel]

theorem measurable_phs : Measurable phs := by
  unfold phs
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)

theorem measurable_nsq {n : Type*} [Fintype n] : Measurable (nsq (n := n)) := by
  unfold nsq
  apply Continuous.measurable
  fun_prop

theorem measurable_rot {m : ℕ} (i j : Fin (m + 1)) : Measurable fun v : Fin (m + 1) → ℂ => rot v i j := by
  have hfun : (fun v : Fin (m + 1) → ℂ => rot v i j) = fun v =>
      if v = 0 then (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i j else hh (v - rz v • e0v m) i j := by
    funext v; unfold rot; split_ifs <;> rfl
  rw [hfun]
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  have hz : Measurable (rz (m := m)) := by
    unfold rz
    exact ((Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_nsq)).neg).mul
      (measurable_phs.comp (measurable_pi_apply 0))
  have hw : Measurable fun v : Fin (m + 1) → ℂ => v - rz v • e0v m :=
    measurable_id.sub (hz.smul_const _)
  unfold hh
  simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.star_apply]
  refine measurable_const.sub (Measurable.mul ?_ ?_)
  · exact Complex.measurable_ofReal.comp (measurable_const.div (measurable_nsq.comp hw))
  · exact ((measurable_pi_apply i).comp hw).mul
      (continuous_star.measurable.comp ((measurable_pi_apply j).comp hw))

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

/-- Conditional rotation: if each `T ω` preserves `γ`, then `(ω, x) ↦ (ω, T ω x)` preserves `ν ⊗ γ`. -/
theorem cond_rot {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (ν : Measure Ω) (γ : Measure E)
    [SFinite ν] [SFinite γ] (T : Ω → E → E) (hT : Measurable fun p : Ω × E => T p.1 p.2)
    (hinv : ∀ ω, γ.map (T ω) = γ) :
    MeasurePreserving (fun p : Ω × E => (p.1, T p.1 p.2)) (ν.prod γ) (ν.prod γ) := by
  have hf : Measurable fun p : Ω × E => (p.1, T p.1 p.2) := measurable_fst.prodMk hT
  refine ⟨hf, ?_⟩
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hf hs), Measure.prod_apply hs]
  refine lintegral_congr fun ω => ?_
  have hTω : Measurable (T ω) := hT.comp measurable_prodMk_left
  have hsec : MeasurableSet (Prod.mk ω ⁻¹' s) := measurable_prodMk_left hs
  conv_rhs => rw [← hinv ω]
  rw [Measure.map_apply hTω hsec]
  rfl

noncomputable abbrev cgRow (n : ℕ) : Measure (Fin n → ℂ) :=
  Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian

theorem left_inv (M N : ℕ) {U : Matrix (Fin M) (Fin M) ℂ} (hU : U ∈ unitaryGroup (Fin M) ℂ) :
    (SpikedWishart.SoftEdge.sampleLaw M N).map (fun X => fun m j => (U * Matrix.of X) m j) =
      SpikedWishart.SoftEdge.sampleLaw M N := by
  have h := sample_invariant M N 1 Uᵀ (one_mem _) (transpose_mem_unitary hU)
  convert h using 2
  funext X m j
  rw [Matrix.one_mul, ← Matrix.transpose_mul, Matrix.transpose_apply]

theorem right_inv (M N : ℕ) {V : Matrix (Fin N) (Fin N) ℂ} (hV : V ∈ unitaryGroup (Fin N) ℂ) :
    (SpikedWishart.SoftEdge.sampleLaw M N).map (fun X => fun m j => (Matrix.of X * V) m j) =
      SpikedWishart.SoftEdge.sampleLaw M N := by
  have h := sample_invariant M N Vᵀ 1 (transpose_mem_unitary hV) (one_mem _)
  convert h using 2
  funext X m j
  rw [Matrix.mul_one, ← Matrix.transpose_mul, Matrix.transpose_apply]

theorem colSplit_mp (M N' : ℕ) :
    MeasurePreserving (fun X : Fin M → Fin (N' + 1) → ℂ => ((fun m => X m 0), fun m j => X m j.succ))
      (SpikedWishart.SoftEdge.sampleLaw M (N' + 1))
      ((cgRow M).prod (SpikedWishart.SoftEdge.sampleLaw M N')) := by
  have h1 : MeasurePreserving (fun (X : Fin M → Fin (N' + 1) → ℂ) (m : Fin M) =>
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N' + 1) => ℂ) 0 (X m))
      (SpikedWishart.SoftEdge.sampleLaw M (N' + 1))
      (Measure.pi fun _ : Fin M => (SpikedWishart.SoftEdge.stdComplexGaussian).prod (cgRow N')) := by
    unfold SpikedWishart.SoftEdge.sampleLaw
    refine measurePreserving_pi _ _ fun _ => ?_
    have := measurePreserving_piFinSuccAbove (fun _ : Fin (N' + 1) => SpikedWishart.SoftEdge.stdComplexGaussian) 0
    exact this
  have h2 := measurePreserving_arrowProdEquivProdArrow ℂ (Fin N' → ℂ) (Fin M)
    (fun _ => SpikedWishart.SoftEdge.stdComplexGaussian) (fun _ => cgRow N')
  have h := h2.comp h1
  convert h using 1
  all_goals (try unfold SpikedWishart.SoftEdge.sampleLaw)
  all_goals (try (funext X; simp [MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.piFinSuccAbove_apply,
    Fin.insertNthEquiv, Fin.removeNth, Equiv.arrowProdEquivProdArrow]))
  all_goals (try rfl)

theorem rowSplit_mp (M' N : ℕ) :
    MeasurePreserving (fun R : Fin (M' + 1) → Fin N → ℂ => (R 0, fun i => R i.succ))
      (SpikedWishart.SoftEdge.sampleLaw (M' + 1) N)
      ((cgRow N).prod (SpikedWishart.SoftEdge.sampleLaw M' N)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (M' + 1) => cgRow N) 0
  unfold SpikedWishart.SoftEdge.sampleLaw
  convert h using 1
  funext R
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
  rfl

/-- Right rotation for rows of any length (identity on length 0). -/
noncomputable def rotN : (n : ℕ) → (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ
  | 0, _ => 1
  | _ + 1, v => rot v

noncomputable def bz : (n : ℕ) → (Fin n → ℂ) → ℂ
  | 0, _ => 0
  | _ + 1, v => rz v

theorem rotN_mem (n : ℕ) (v : Fin n → ℂ) : rotN n v ∈ unitaryGroup (Fin n) ℂ := by
  cases n with
  | zero => exact one_mem _
  | succ m => exact rot_mem v

theorem norm_bz (n : ℕ) (v : Fin n → ℂ) : ‖bz n v‖ = Real.sqrt (nsq v) := by
  cases n with
  | zero => simp [bz, nsq]
  | succ m => exact norm_rz v

theorem rotN_mulVec (n : ℕ) (v : Fin n → ℂ) (j : Fin n) :
    (rotN n v *ᵥ v) j = if (j : ℕ) = 0 then bz n v else 0 := by
  cases n with
  | zero => exact j.elim0
  | succ m =>
    show (rot v *ᵥ v) j = _
    rw [rot_mulVec]
    simp [e0v, bz]

theorem measurable_rotN (n : ℕ) (i j : Fin n) : Measurable fun v : Fin n → ℂ => rotN n v i j := by
  cases n with
  | zero => exact i.elim0
  | succ m => exact measurable_rot i j

/-- Left Householder step on `(g, R)`. -/
noncomputable def stepL {M N' : ℕ} (p : (Fin (M + 1) → ℂ) × (Fin (M + 1) → Fin N' → ℂ)) :
    (Fin (M + 1) → ℂ) × (Fin (M + 1) → Fin N' → ℂ) :=
  (p.1, fun m j => (rot p.1 * Matrix.of p.2) m j)

/-- Right Householder step on `(r, Y)`. -/
noncomputable def stepR {M N' : ℕ} (p : (Fin N' → ℂ) × (Fin M → Fin N' → ℂ)) :
    (Fin N' → ℂ) × (Fin M → Fin N' → ℂ) :=
  (p.1, fun i j => (Matrix.of p.2 * (rotN N' p.1)ᵀ) i j)

theorem stepL_mp (M N' : ℕ) :
    MeasurePreserving (stepL (M := M) (N' := N'))
      ((cgRow (M + 1)).prod (SpikedWishart.SoftEdge.sampleLaw (M + 1) N'))
      ((cgRow (M + 1)).prod (SpikedWishart.SoftEdge.sampleLaw (M + 1) N')) := by
  refine cond_rot _ _ (fun (g : Fin (M + 1) → ℂ) (R : Fin (M + 1) → Fin N' → ℂ) =>
    fun m j => (rot g * Matrix.of R) m j) ?_ ?_
  · refine measurable_pi_iff.mpr fun m => measurable_pi_iff.mpr fun j => ?_
    simp only [mul_apply, Matrix.of_apply]
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((measurable_rot m k).comp measurable_fst).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd))
  · intro g; exact left_inv (M + 1) N' (rot_mem g)

theorem stepR_mp (M N' : ℕ) :
    MeasurePreserving (stepR (M := M) (N' := N'))
      ((cgRow N').prod (SpikedWishart.SoftEdge.sampleLaw M N'))
      ((cgRow N').prod (SpikedWishart.SoftEdge.sampleLaw M N')) := by
  refine cond_rot _ _ (fun (r : Fin N' → ℂ) (Y : Fin M → Fin N' → ℂ) =>
    fun i j => (Matrix.of Y * (rotN N' r)ᵀ) i j) ?_ ?_
  · refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [mul_apply, Matrix.of_apply, Matrix.transpose_apply]
    refine Finset.measurable_sum _ fun k _ => ?_
    have h1 : Measurable fun p : (Fin N' → ℂ) × (Fin M → Fin N' → ℂ) => p.2 i k :=
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd)
    have h2 : Measurable fun p : (Fin N' → ℂ) × (Fin M → Fin N' → ℂ) => rotN N' p.1 j k :=
      (measurable_rotN N' j k).comp measurable_fst
    exact h1.mul h2
  · intro r; exact right_inv M N' (transpose_mem_unitary (rotN_mem N' r))

/-- The array after the left rotation, columns `≥ 1`. -/
noncomputable def R2 {M N' : ℕ} (X : Fin (M + 1) → Fin (N' + 1) → ℂ) : Fin (M + 1) → Fin N' → ℂ :=
  (stepL ((fun m => X m 0), fun m j => X m j.succ)).2

/-- The remainder after both rotations. -/
noncomputable def Yof {M N' : ℕ} (X : Fin (M + 1) → Fin (N' + 1) → ℂ) : Fin M → Fin N' → ℂ :=
  (stepR ((R2 X) 0, fun i => (R2 X) i.succ)).2

theorem law_col0 (M N' : ℕ) :
    MeasurePreserving (fun X : Fin M → Fin (N' + 1) → ℂ => fun m => X m 0)
      (SpikedWishart.SoftEdge.sampleLaw M (N' + 1)) (cgRow M) :=
  measurePreserving_fst.comp (colSplit_mp M N')

theorem law_R2 (M N' : ℕ) :
    MeasurePreserving (R2 (M := M) (N' := N'))
      (SpikedWishart.SoftEdge.sampleLaw (M + 1) (N' + 1)) (SpikedWishart.SoftEdge.sampleLaw (M + 1) N') :=
  measurePreserving_snd.comp ((stepL_mp M N').comp (colSplit_mp (M + 1) N'))

theorem law_row (M N' : ℕ) :
    MeasurePreserving (fun X : Fin (M + 1) → Fin (N' + 1) → ℂ => R2 X 0)
      (SpikedWishart.SoftEdge.sampleLaw (M + 1) (N' + 1)) (cgRow N') :=
  measurePreserving_fst.comp ((rowSplit_mp M N').comp (law_R2 M N'))

theorem law_Yof (M N' : ℕ) :
    MeasurePreserving (Yof (M := M) (N' := N'))
      (SpikedWishart.SoftEdge.sampleLaw (M + 1) (N' + 1)) (SpikedWishart.SoftEdge.sampleLaw M N') :=
  measurePreserving_snd.comp ((stepR_mp M N').comp ((rowSplit_mp M N').comp (law_R2 M N')))

/-- The Golub-Kahan step identity `U G W = [[z, b e₀ᵀ], [0, Y]]`. -/
theorem gk_identity {M N' : ℕ} (X : Fin (M + 1) → Fin (N' + 1) → ℂ) :
    rot (fun m => X m 0) * Matrix.of X * blk1 (rotN N' (R2 X 0))ᵀ =
      Kblk (rz (fun m => X m 0)) (bz N' (R2 X 0)) (Matrix.of (Yof X)) := by
  have hR2 : ∀ i l, R2 X i l = ∑ k, rot (fun m => X m 0) i k * X k l.succ := by
    intro i l; simp [R2, stepL, mul_apply]
  have hg := rot_mulVec (fun m => X m 0)
  have hr := rotN_mulVec N' (R2 X 0)
  ext i j
  rw [mul_apply, Fin.sum_univ_succ]
  cases j using Fin.cases with
  | zero =>
    have hcol : (rot (fun m => X m 0) * Matrix.of X) i 0 = (rz (fun m => X m 0) • e0v M) i := by
      rw [← hg]; simp [mul_apply, mulVec, dotProduct]
    simp only [blk1, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mul_zero,
      Finset.sum_const_zero, add_zero, mul_one, hcol]
    cases i using Fin.cases <;> simp [Kblk, e0v]
  | succ j' =>
    have hrow : ∀ l : Fin N', (rot (fun m => X m 0) * Matrix.of X) i l.succ = R2 X i l := by
      intro l; rw [hR2]; simp [mul_apply]
    simp only [blk1, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add, hrow,
      Matrix.transpose_apply]
    cases i using Fin.cases with
    | zero =>
      have h1 := hr j'
      simp only [mulVec, dotProduct] at h1
      rw [show (∑ i, R2 X 0 i * rotN N' (R2 X 0) j' i) = ∑ i, rotN N' (R2 X 0) j' i * R2 X 0 i from
        Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
      simp [Kblk]
    | succ i' =>
      simp [Kblk, Yof, stepR, mul_apply, Matrix.transpose_apply]

/-- Deterministic step: `Dec` of the remainder gives `Dec` of the array. -/
theorem dec_step {M N' : ℕ} {α β : ℝ} (X : Fin (M + 1) → Fin (N' + 1) → ℂ)
    (hg : Real.sqrt (nsq (fun m => X m 0)) ≤ α) (hr : Real.sqrt (nsq (R2 X 0)) ≤ β)
    (hY : Dec (Matrix.of (Yof X)) α β) : Dec (Matrix.of X) α β := by
  set U := rot (fun m => X m 0)
  set W := blk1 (rotN N' (R2 X 0))ᵀ
  have hU : U ∈ unitaryGroup (Fin (M + 1)) ℂ := rot_mem _
  have hW : W ∈ unitaryGroup (Fin (N' + 1)) ℂ := blk1_mem (transpose_mem_unitary (rotN_mem _ _))
  have hK : Dec (U * Matrix.of X * W) α β := by
    rw [gk_identity]
    exact Dec_Kblk (by rw [norm_rz]; exact hg) (by rw [norm_bz]; exact hr) hY
  have hW0 : ∀ k j : Fin (N' + 1), (j : ℕ) = 0 → (k : ℕ) ≠ 0 → (star W) k j = 0 := by
    simp only [W]; rw [blk1_star]; exact blk1_col0 _
  have hsU : star U ∈ unitaryGroup (Fin (M + 1)) ℂ :=
    mem_unitaryGroup_iff.mpr (by rw [star_star]; exact mem_unitaryGroup_iff'.mp hU)
  have hsW : star W ∈ unitaryGroup (Fin (N' + 1)) ℂ :=
    mem_unitaryGroup_iff.mpr (by rw [star_star]; exact mem_unitaryGroup_iff'.mp hW)
  have h := hK.unitary hsU hsW hW0
  have e : star U * (U * Matrix.of X * W) * star W = Matrix.of X := by
    rw [show star U * (U * Matrix.of X * W) * star W = (star U * U) * Matrix.of X * (W * star W) by
      simp only [Matrix.mul_assoc]]
    rw [mem_unitaryGroup_iff'.mp hU, mem_unitaryGroup_iff.mp hW, Matrix.one_mul, Matrix.mul_one]
  rwa [e] at h

end

-- ===== from Q1d.lean =====
section

/-! Q1 = `P2_nullEdge`: induction over the Golub-Kahan steps, Chernoff bounds for `Γ(m,1)` tails, and
the final edge estimate. Needs ChildStatements, LamMax, Misc, SchurEig, BlockForm, Q1a, Q1b, Q3a, Q3b, Q1c. -/

theorem bnd_zero_mat {m n : Type*} [Fintype m] [Fintype n] (β : ℝ) : Bnd (0 : Matrix m n ℂ) β := by
  intro v
  rw [zero_mulVec]
  simp only [nsq, Pi.zero_apply, map_zero, Finset.sum_const_zero]
  exact mul_nonneg (sq_nonneg _) (nsq_nonneg _)

theorem dec_of_bnd {M N : ℕ} {G : Matrix (Fin M) (Fin N) ℂ} {α β : ℝ} (h : Bnd G α) : Dec G α β :=
  ⟨G, 0, by rw [add_zero], h, bnd_zero_mat β, fun _ _ _ => rfl⟩

theorem bnd_zero_col {M : ℕ} (G : Matrix (Fin M) (Fin 0) ℂ) (α : ℝ) : Bnd G α := by
  have : G = 0 := by ext i j; exact j.elim0
  rw [this]; exact bnd_zero_mat α

theorem bnd_zero_row {N : ℕ} (G : Matrix (Fin 0) (Fin N) ℂ) (α : ℝ) : Bnd G α := by
  have : G = 0 := by ext i j; exact i.elim0
  rw [this]; exact bnd_zero_mat α

theorem measurableSet_thr (n : ℕ) (a : ℝ) : MeasurableSet {v : Fin n → ℂ | a < Real.sqrt (nsq v)} :=
  measurableSet_lt measurable_const (Real.continuous_sqrt.measurable.comp measurable_nsq)

/-- Failure probability of the bidiagonal decomposition. -/
theorem fail_bound (α β : ℝ) (ε1 ε2 : ℝ≥0∞) : ∀ (N M : ℕ),
    (∀ m ≤ M, cgRow m {v | α < Real.sqrt (nsq v)} ≤ ε1) →
    (∀ m ≤ N, cgRow m {v | β < Real.sqrt (nsq v)} ≤ ε2) →
    SpikedWishart.SoftEdge.sampleLaw M N {X | ¬ Dec (Matrix.of X) α β} ≤ N * (ε1 + ε2)
  | 0, M, _, _ => by
    have : {X : Fin M → Fin 0 → ℂ | ¬ Dec (Matrix.of X) α β} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact dec_of_bnd (bnd_zero_col _ α)
    rw [this, measure_empty]; exact bot_le
  | N' + 1, 0, _, _ => by
    have : {X : Fin 0 → Fin (N' + 1) → ℂ | ¬ Dec (Matrix.of X) α β} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact dec_of_bnd (bnd_zero_row _ α)
    rw [this, measure_empty]; exact bot_le
  | N' + 1, M' + 1, h1, h2 => by
    have hsub : {X : Fin (M' + 1) → Fin (N' + 1) → ℂ | ¬ Dec (Matrix.of X) α β} ⊆
        ((fun X : Fin (M' + 1) → Fin (N' + 1) → ℂ => fun m => X m 0) ⁻¹' {v | α < Real.sqrt (nsq v)} ∪
          (fun X : Fin (M' + 1) → Fin (N' + 1) → ℂ => R2 X 0) ⁻¹' {v | β < Real.sqrt (nsq v)}) ∪
          Yof ⁻¹' {Y | ¬ Dec (Matrix.of Y) α β} := by
      intro X hX
      by_contra hc
      simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or, not_lt, not_not] at hc
      exact hX (dec_step X hc.1.1 hc.1.2 hc.2)
    have hA := (law_col0 (M' + 1) N').measure_preimage (measurableSet_thr (M' + 1) α).nullMeasurableSet
    have hB := (law_row M' N').measure_preimage (measurableSet_thr N' β).nullMeasurableSet
    have hC : SpikedWishart.SoftEdge.sampleLaw (M' + 1) (N' + 1) (Yof ⁻¹' {Y | ¬ Dec (Matrix.of Y) α β}) ≤
        SpikedWishart.SoftEdge.sampleLaw M' N' {Y | ¬ Dec (Matrix.of Y) α β} := by
      have := Measure.le_map_apply (μ := SpikedWishart.SoftEdge.sampleLaw (M' + 1) (N' + 1))
        (law_Yof M' N').measurable.aemeasurable
        {Y : Fin M' → Fin N' → ℂ | ¬ Dec (Matrix.of Y) α β}
      rwa [(law_Yof M' N').map_eq] at this
    have ih := fail_bound α β ε1 ε2 N' M' (fun m hm => h1 m (by omega)) (fun m hm => h2 m (by omega))
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ (ε1 + ε2) + (N' : ℝ≥0∞) * (ε1 + ε2) := by
        gcongr
        · refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
          · rw [hA]; exact h1 _ le_rfl
          · rw [hB]; exact h2 _ (by omega)
        · exact hC.trans ih
      _ = ((N' + 1 : ℕ) : ℝ≥0∞) * (ε1 + ε2) := by push_cast; ring

theorem gauss_mgf (l : ℝ) :
    ∫ x, Real.exp (l * x ^ 2) ∂(ProbabilityTheory.gaussianReal 0 (1 / 2)) =
      (Real.sqrt Real.pi)⁻¹ * Real.sqrt (Real.pi / (1 - l)) := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h : ∀ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 (1 / 2) x • Real.exp (l * x ^ 2) =
      (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1 - l) * x ^ 2) := by
    intro x
    rw [ProbabilityTheory.gaussianPDFReal, smul_eq_mul]
    have h2 : (2 * Real.pi * ((1 / 2 : NNReal) : ℝ)) = Real.pi := by push_cast; ring
    have h3 : (-(x - 0) ^ 2 / (2 * ((1 / 2 : NNReal) : ℝ))) = -x ^ 2 := by push_cast; ring
    rw [h2, h3, mul_assoc, ← Real.exp_add]
    congr 2; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]

theorem cg_mgf (l : ℝ) (hl : l < 1) :
    ∫ z, Real.exp (l * Complex.normSq z) ∂SpikedWishart.SoftEdge.stdComplexGaussian = 1 / (1 - l) := by
  have hf : AEStronglyMeasurable (fun z : ℂ => Real.exp (l * Complex.normSq z))
      SpikedWishart.SoftEdge.stdComplexGaussian :=
    (Real.continuous_exp.comp (continuous_const.mul Complex.continuous_normSq)).aestronglyMeasurable
  unfold SpikedWishart.SoftEdge.stdComplexGaussian at hf ⊢
  rw [integral_map (φ := fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable hf]
  have h : ∀ p : ℝ × ℝ, Real.exp (l * Complex.normSq (⟨p.1, p.2⟩ : ℂ)) =
      Real.exp (l * p.1 ^ 2) * Real.exp (l * p.2 ^ 2) := by
    intro p; rw [← Real.exp_add, Complex.normSq_mk]; congr 1; ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => Real.exp (l * x ^ 2)) (fun y : ℝ => Real.exp (l * y ^ 2)),
    gauss_mgf l]
  have hpi := Real.pi_pos
  have h1l : 0 < 1 - l := by linarith
  rw [← sq, mul_pow, inv_pow, Real.sq_sqrt hpi.le, Real.sq_sqrt (div_nonneg hpi.le h1l.le)]
  field_simp

theorem row_mgf (m : ℕ) (l : ℝ) (hl : l < 1) :
    ∫ v, Real.exp (l * nsq v) ∂cgRow m = (1 / (1 - l)) ^ m := by
  have h : ∀ v : Fin m → ℂ, Real.exp (l * nsq v) = ∏ i, Real.exp (l * Complex.normSq (v i)) := by
    intro v; rw [nsq, Finset.mul_sum, Real.exp_sum]
  simp_rw [h]
  rw [show (∫ v, ∏ i, Real.exp (l * Complex.normSq (v i)) ∂cgRow m) =
      ∏ i : Fin m, ∫ z, Real.exp (l * Complex.normSq z) ∂SpikedWishart.SoftEdge.stdComplexGaussian from
    integral_fintype_prod_eq_prod (fun _ z => Real.exp (l * Complex.normSq z))]
  rw [Finset.prod_congr rfl (fun _ _ => cg_mgf l hl), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem chernoff (m : ℕ) (l t : ℝ) (hl0 : 0 ≤ l) (hl : l < 1) :
    (cgRow m).real {v | t < nsq v} ≤ (1 / (1 - l)) ^ m / Real.exp (l * t) := by
  have h1l : 0 < 1 - l := by linarith
  have hint : Integrable (fun v => Real.exp (l * nsq v)) (cgRow m) := by
    apply Integrable.of_integral_ne_zero
    rw [row_mgf m l hl]
    positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun v => (Real.exp_pos (l * nsq v)).le) hint (Real.exp (l * t))
  rw [row_mgf m l hl] at hmk
  have hsub : {v : Fin m → ℂ | t < nsq v} ⊆ {v | Real.exp (l * t) ≤ Real.exp (l * nsq v)} := by
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv.le hl0)
  have hmono := measureReal_mono (μ := cgRow m) hsub (measure_ne_top _ _)
  rw [le_div_iff₀ (Real.exp_pos _)]
  calc (cgRow m).real {v | t < nsq v} * Real.exp (l * t) ≤
        (cgRow m).real {v | Real.exp (l * t) ≤ Real.exp (l * nsq v)} * Real.exp (l * t) :=
        mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
    _ = Real.exp (l * t) * (cgRow m).real {v | Real.exp (l * t) ≤ Real.exp (l * nsq v)} := mul_comm _ _
    _ ≤ _ := hmk

theorem tail_bound (m M : ℕ) (δ t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hm : m ≤ M)
    (ht : (m : ℝ) + δ * M ≤ t) :
    (cgRow m).real {v | t < nsq v} ≤ Real.exp (-(δ ^ 2 * M / 8)) := by
  set l := δ / 4
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 / 4 := by simp only [l]; linarith
  have h1l : 0 < 1 - l := by linarith
  refine (chernoff m l t hl0 (by linarith)).trans ?_
  have hb : 1 / (1 - l) ≤ Real.exp (l + 2 * l ^ 2) := by
    have e1 : 1 / (1 - l) = l / (1 - l) + 1 := by field_simp; ring
    have e2 : l / (1 - l) ≤ l + 2 * l ^ 2 := by
      rw [div_le_iff₀ h1l]; nlinarith
    rw [e1]
    exact (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr e2)
  have hpow : (1 / (1 - l)) ^ m ≤ Real.exp ((m : ℝ) * (l + 2 * l ^ 2)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hb m
  rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  refine hpow.trans (Real.exp_le_exp.mpr ?_)
  have hmM : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : l * t ≥ l * ((m : ℝ) + δ * M) := mul_le_mul_of_nonneg_left ht hl0
  simp only [l] at this ⊢
  nlinarith

/-- A bound `‖G v‖ ≤ γ ‖v‖` gives `λ₁((1/M) G* G) ≤ γ²/M`. -/
theorem lam_le_of_bnd (M N : ℕ) [NeZero N] (X : Fin M → Fin N → ℂ) (γ : ℝ)
    (h : Bnd (Matrix.of X) γ) : largestEig M 1 (fun _ => 1) X ≤ γ ^ 2 / M := by
  rw [largestEig_le_iff, eig_le_iff_posSemidef]
  have hS := sampleCov_isHermitian M 1 (fun _ => (1 : ℝ)) X
  rw [psd_iff_re (isHermitian_smul_one_sub hS _)]
  intro v
  set D := dataMat M (fun _ => (1 : ℝ)) X
  set c : ℝ := (Real.sqrt M)⁻¹
  have hc : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = (M : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg M)]; push_cast; ring
  have hSY : sampleCov M 1 (fun _ => (1 : ℝ)) X = (((c : ℂ)) • Dᴴ)ᴴ * ((c : ℂ) • Dᴴ) := by
    rw [sampleCov_one_eq, conjTranspose_smul, conjTranspose_conjTranspose, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    congr 1
    rw [RCLike.star_def, Complex.conj_ofReal, hc]
  rw [hSY, re_quad_sub_gram]
  have hD : ∀ k, (((c : ℂ) • Dᴴ) *ᵥ v) k = (c : ℂ) * star ((Matrix.of X *ᵥ star v) k) := by
    intro k
    simp only [smul_mulVec, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp only [mulVec, dotProduct, conjTranspose_apply, D, dataMat, Matrix.of_apply, star_sum,
      Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Real.sqrt_one, mul_comm]
  simp_rw [hD, Complex.normSq_mul, Complex.normSq_ofReal]
  have hconj : ∀ k, Complex.normSq (star ((Matrix.of X *ᵥ star v) k)) =
      Complex.normSq ((Matrix.of X *ᵥ star v) k) := fun k => by
    rw [RCLike.star_def, Complex.normSq_conj]
  simp_rw [hconj]
  rw [← Finset.mul_sum]
  have hb := h (star v)
  have hsv : nsq (star v) = nsq v := by
    simp only [nsq, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [RCLike.star_def, Complex.normSq_conj]
  rw [hsv] at hb
  change 0 ≤ γ ^ 2 / M * nsq v - c * c * nsq (Matrix.of X *ᵥ star v)
  have hcc : c * c = 1 / M := by
    simp only [c]; rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg M)]; ring
  rw [hcc]
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rw [div_mul_eq_mul_div, one_div_mul_eq_div, ← sub_div]
  exact div_nonneg (by linarith) hM

/-- Numerical step: `(√(1+δ) + √(y+δ))² ≤ (1+√y)² + ε` for `δ = η²`, `η ≤ min(1/2, ε/24)`, `y ≤ 1`. -/
theorem edge_num (y ε η : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2)
    (hη2 : η ≤ ε / 24) :
    (Real.sqrt (1 + η ^ 2) + Real.sqrt (y + η ^ 2)) ^ 2 ≤ (1 + Real.sqrt y) ^ 2 + ε := by
  have hs1 : Real.sqrt (1 + η ^ 2) ≤ 1 + η := by
    rw [show (1 + η) = Real.sqrt ((1 + η) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsy := Real.sqrt_nonneg y
  have hsy1 : Real.sqrt y ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hy1
  have hs2 : Real.sqrt (y + η ^ 2) ≤ Real.sqrt y + η := by
    rw [show (Real.sqrt y + η) = Real.sqrt ((Real.sqrt y + η) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    have := Real.sq_sqrt hy0
    nlinarith
  have h0 : 0 ≤ Real.sqrt (1 + η ^ 2) + Real.sqrt (y + η ^ 2) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hle : Real.sqrt (1 + η ^ 2) + Real.sqrt (y + η ^ 2) ≤ 1 + Real.sqrt y + 2 * η := by linarith
  calc _ ≤ (1 + Real.sqrt y + 2 * η) ^ 2 := pow_le_pow_left₀ h0 hle 2
    _ ≤ (1 + Real.sqrt y) ^ 2 + ε := by nlinarith

/-- Fixed-size edge bound. -/
theorem edge_fixed (Mn Nn : ℕ) (h1 : 1 ≤ Nn) (h2 : Nn ≤ Mn) (ε η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hη2 : η ≤ ε / 24) :
    (SpikedWishart.SoftEdge.sampleLaw Mn Nn).real
        {X | (1 + Real.sqrt ((Nn : ℝ) / Mn)) ^ 2 + ε < largestEig Mn 1 (fun _ => 1) X} ≤
      2 * (Mn : ℝ) * Real.exp (-((η ^ 2) ^ 2 * Mn / 8)) := by
  have : NeZero Nn := ⟨by omega⟩
  set δ := η ^ 2
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by simp only [δ]; nlinarith
  have hMpos : (0 : ℝ) < Mn := by exact_mod_cast (show 0 < Mn by omega)
  set α := Real.sqrt (Mn * (1 + δ))
  set β := Real.sqrt (Nn + δ * Mn)
  have hα : 0 ≤ α := Real.sqrt_nonneg _
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  set y : ℝ := (Nn : ℝ) / Mn
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by
    simp only [y]; rw [div_le_one hMpos]; exact_mod_cast h2
  -- the event lies in the failure set
  have hsub : {X : Fin Mn → Fin Nn → ℂ |
      (1 + Real.sqrt ((Nn : ℝ) / Mn)) ^ 2 + ε < largestEig Mn 1 (fun _ => 1) X} ⊆
      {X | ¬ Dec (Matrix.of X) α β} := by
    intro X hX hD
    have hl := lam_le_of_bnd Mn Nn X (α + β) (hD.bnd hα hβ)
    have hαe : α = Real.sqrt Mn * Real.sqrt (1 + δ) := Real.sqrt_mul (Nat.cast_nonneg _) _
    have hβe : β = Real.sqrt Mn * Real.sqrt (y + δ) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
      show Real.sqrt ((Nn : ℝ) + δ * Mn) = _
      congr 1; simp only [y]; field_simp; (try ring)
    have hval : (α + β) ^ 2 / Mn = (Real.sqrt (1 + δ) + Real.sqrt (y + δ)) ^ 2 := by
      rw [hαe, hβe, ← mul_add, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      field_simp
    have := edge_num y ε η hy0 hy1 hη0.le hη1 hη2
    simp only [Set.mem_setOf_eq] at hX
    have : largestEig Mn 1 (fun _ => 1) X ≤ (1 + Real.sqrt y) ^ 2 + ε := by
      rw [hval] at hl; exact hl.trans this
    linarith
  set e := Real.exp (-(δ ^ 2 * Mn / 8))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hthr : ∀ (m : ℕ) (a : ℝ), 0 ≤ a →
      {v : Fin m → ℂ | a < Real.sqrt (nsq v)} = {v | a ^ 2 < nsq v} := by
    intro m a ha; ext v; simp only [Set.mem_setOf_eq]; exact Real.lt_sqrt ha
  have hA : ∀ m ≤ Mn, cgRow m {v | α < Real.sqrt (nsq v)} ≤ ENNReal.ofReal e := by
    intro m hm
    rw [hthr m α hα, ← ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    apply tail_bound m Mn δ _ hδ0 hδ1 hm
    rw [Real.sq_sqrt (by positivity)]
    have : (m : ℝ) ≤ Mn := by exact_mod_cast hm
    nlinarith
  have hB : ∀ m ≤ Nn, cgRow m {v | β < Real.sqrt (nsq v)} ≤ ENNReal.ofReal e := by
    intro m hm
    rw [hthr m β hβ, ← ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    apply tail_bound m Mn δ _ hδ0 hδ1 (hm.trans h2)
    rw [Real.sq_sqrt (by positivity)]
    have : (m : ℝ) ≤ Nn := by exact_mod_cast hm
    linarith
  have hF := fail_bound α β (ENNReal.ofReal e) (ENNReal.ofReal e) Nn Mn hA hB
  have hfin : (Nn : ℝ≥0∞) * (ENNReal.ofReal e + ENNReal.ofReal e) ≠ ∞ := by
    apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  calc _ ≤ (SpikedWishart.SoftEdge.sampleLaw Mn Nn).real {X | ¬ Dec (Matrix.of X) α β} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ((Nn : ℝ≥0∞) * (ENNReal.ofReal e + ENNReal.ofReal e)).toReal := by
        rw [measureReal_def]; exact ENNReal.toReal_mono hfin hF
    _ = (Nn : ℝ) * (2 * e) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal he, ENNReal.toReal_natCast]; ring
    _ ≤ 2 * (Mn : ℝ) * e := by
        have : (Nn : ℝ) ≤ Mn := by exact_mod_cast h2
        nlinarith

end

-- ===== from QE.lean =====
section

/-- For `N = 0` the bad event is empty (`largestEig` over `Fin 0` is `0`). -/
theorem edge_zero (Mn : ℕ) (ε : ℝ) (hε : 0 < ε) :
    {X : Fin Mn → Fin 0 → ℂ | (1 + Real.sqrt ((0 : ℕ) / (Mn : ℝ))) ^ 2 + ε <
      largestEig Mn 1 (fun _ => 1) X} = ∅ := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  have h0 : largestEig Mn 1 (fun _ => 1) X = 0 := by
    unfold largestEig
    exact Real.iSup_of_isEmpty _
  rw [h0]
  positivity

theorem p2_edgeRate : P2_edgeRate := by
  intro ε hε l M N hM hNM
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (1 / 2) (ε / 24) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min (by norm_num) (by linarith)
  have hη1 : η ≤ 1 / 2 := by rw [hη]; exact min_le_left _ _
  have hη2 : η ≤ ε / 24 := by rw [hη]; exact min_le_right _ _
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (η ^ 2) ^ 2 / 8 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hMr : Tendsto (fun n => (M n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hM
  have hbound : ∀ n, (M n : ℝ) ^ l * (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
      {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X} ≤
        2 * (M n : ℝ) ^ (l + 1) * Real.exp (-(c * M n)) := by
    intro n
    have hMl : (0 : ℝ) ≤ (M n : ℝ) ^ l := pow_nonneg (Nat.cast_nonneg _) l
    have hE : 0 ≤ 2 * (M n : ℝ) ^ (l + 1) * Real.exp (-(c * M n)) := by positivity
    rcases Nat.eq_zero_or_pos (N n) with h0 | hpos
    · have hset := edge_zero (M n) ε hε
      have h0' : (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
          {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X} = 0 := by
        revert hset
        generalize N n = q at h0 ⊢
        subst h0
        intro hset
        rw [hset, measureReal_empty]
      rw [h0', mul_zero]; exact hE
    · have h := edge_fixed (M n) (N n) hpos (hNM n) ε η hη0 hη1 hη2
      have he : -((η ^ 2) ^ 2 * (M n : ℝ) / 8) = -(c * M n) := by rw [hc]; ring
      rw [he] at h
      have h2 := mul_le_mul_of_nonneg_left h hMl
      have he2 : (M n : ℝ) ^ l * (2 * (M n : ℝ) * Real.exp (-(c * M n))) =
          2 * (M n : ℝ) ^ (l + 1) * Real.exp (-(c * M n)) := by ring
      linarith
  have hlim : Tendsto (fun n => 2 * (M n : ℝ) ^ (l + 1) * Real.exp (-(c * M n))) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (l + 1)).comp
      ((tendsto_id.const_mul_atTop hc0).comp hMr)
    have h2 := h1.const_mul (2 * (c ^ (l + 1))⁻¹)
    rw [mul_zero] at h2
    refine h2.congr (fun n => ?_)
    simp only [Function.comp, id]
    have hc4 : c ^ (l + 1) ≠ 0 := pow_ne_zero _ hc0.ne'
    rw [mul_pow]
    field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) l) measureReal_nonneg) hbound

end

end SpikedWishart.Separated.Lib

open SpikedWishart.Separated in
theorem solution :
  ∀ (ε : ℝ), 0 < ε → ∀ (l : ℕ) (M N : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, N n ≤ M n) →
    Tendsto (fun n => (M n : ℝ) ^ l * (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X})
      atTop (𝓝 0) := by
  exact SpikedWishart.Separated.Lib.p2_edgeRate
