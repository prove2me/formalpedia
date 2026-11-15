-- Prove2me | solution 2 for StrongConv.prob_norm_adjPerp_le_highDegree_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T13:19:42.944345+00:00
-- url     : https://prove2.me/submissions/c07977a5-022a-4dc3-ba7a-3b05260fbfc8

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_sudakov_fernique
import Theorems.Thm_GaussianMatrix_gaussian_concentration_vector

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-!
# Blueprint T38: Brailovskaya–van Handel Theorem 3.8 for random regular graphs, proved directly

A Lindeberg replacement on the trace function `M ↦ tr (1 + θ M / n) ^ n` (`n` even) compares
`Y = ∑ᵢ (Πᵢ + Πᵢᵀ − (2/N) J)` with the Gaussian matrix `G = ∑ᵢ (N − 1)^(-1/2) P (Wᵢ + Wᵢᵀ) P`,
which has the same entry covariance; the norm of `G` is controlled by the Sudakov–Fernique
inequality and Gaussian concentration (both Proved on prove2.me as `GaussianMatrix.*`).
Every lemma here is a stub; `T38Part<X>.lean` proves them.
-/
/-- Real `N × N` matrices, normed by the `ℓ² → ℓ²` operator norm. -/
abbrev Mat (N : ℕ) := Matrix (Fin N) (Fin N) ℝ

/-- `P = I − J/N`, the orthogonal projection onto `{1}⊥`. -/
def pMat (N : ℕ) : Mat N := 1 - (1 / (N : ℝ)) • Matrix.of (fun _ _ => (1 : ℝ))

/-- The centred summand `Π_τ + Π_τᵀ − (2/N) J`, with `Π_τ e_b = e_{τ b}`. -/
def xMat {N : ℕ} (τ : Equiv.Perm (Fin N)) : Mat N :=
  Matrix.of fun a b => (if τ b = a then (1 : ℝ) else 0) + (if τ a = b then 1 else 0) - 2 / (N : ℝ)

/-- `Y(σ) = ∑ᵢ xMat (σ i)`. -/
def xSum {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Mat N := ∑ i, xMat (σ i)

/-- The Gaussian summand `(N − 1)^(-1/2) · P (W + Wᵀ) P` for `W = (w (a, b))`. -/
def gMat {N : ℕ} (w : Fin N × Fin N → ℝ) : Mat N :=
  (Real.sqrt ((N : ℝ) - 1))⁻¹ •
    (pMat N * (Matrix.of (fun a b => w (a, b)) + Matrix.of (fun a b => w (b, a))) * pMat N)

/-- `G(w) = ∑ᵢ gMat (w i)`. -/
def gSum {d N : ℕ} (w : Fin d → Fin N × Fin N → ℝ) : Mat N := ∑ i, gMat (w i)

/-- The standard Gaussian measure on `ℝ^(N × N)`. -/
def gauss (N : ℕ) : Measure (Fin N × Fin N → ℝ) := Measure.pi fun _ => gaussianReal 0 1

/-- `d` independent copies of `gauss N`. -/
def gaussPow (d N : ℕ) : Measure (Fin d → Fin N × Fin N → ℝ) := Measure.pi fun _ => gauss N

/-- The test function `F(M) = tr (1 + θ M / n) ^ n`. -/
def Fn {N : ℕ} (θ : ℝ) (n : ℕ) (M : Mat N) : ℝ := Matrix.trace ((1 + (θ / (n : ℝ)) • M) ^ n)

/-- `F(M) + N`. -/
def Ft {N : ℕ} (θ : ℝ) (n : ℕ) (M : Mat N) : ℝ := Fn θ n M + N

/-- The first-order Taylor term of `W ↦ Fn θ n (M + W)` at `W = 0`. -/
def linTerm {N : ℕ} (θ : ℝ) (n : ℕ) (M W : Mat N) : ℝ :=
  θ * Matrix.trace (W * (1 + (θ / (n : ℝ)) • M) ^ (n - 1))

/-- The second-order Taylor term of `W ↦ Fn θ n (M + W)` at `W = 0`. -/
def quadTerm {N : ℕ} (θ : ℝ) (n : ℕ) (M W : Mat N) : ℝ :=
  θ ^ 2 / (2 * (n : ℝ)) * ∑ a ∈ Finset.range (n - 1),
    Matrix.trace (W * (1 + (θ / (n : ℝ)) • M) ^ a * W * (1 + (θ / (n : ℝ)) • M) ^ (n - 2 - a))

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartL
/-!
# T38 Part L: spectral toolkit for real symmetric matrices
-/
/-- The spectral theorem, written out as a product. -/
theorem eq_conj {N : ℕ} (B : Mat N) (hB : B.IsHermitian) :
    B = (hB.eigenvectorUnitary : Mat N) * diagonal hB.eigenvalues *
      star (hB.eigenvectorUnitary : Mat N) := by
  have h := hB.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa using h

theorem star_mul_self' {N : ℕ} (B : Mat N) (hB : B.IsHermitian) :
    star (hB.eigenvectorUnitary : Mat N) * (hB.eigenvectorUnitary : Mat N) = 1 :=
  Unitary.coe_star_mul_self _

theorem self_mul_star' {N : ℕ} (B : Mat N) (hB : B.IsHermitian) :
    (hB.eigenvectorUnitary : Mat N) * star (hB.eigenvectorUnitary : Mat N) = 1 :=
  Unitary.coe_mul_star_self _

/-- Powers in the eigenbasis. -/
theorem pow_eq_conj {N : ℕ} (B : Mat N) (hB : B.IsHermitian) (m : ℕ) :
    B ^ m = (hB.eigenvectorUnitary : Mat N) * diagonal (fun i => hB.eigenvalues i ^ m) *
      star (hB.eigenvectorUnitary : Mat N) := by
  induction m with
  | zero =>
    simp only [pow_zero]
    rw [show (diagonal fun _ : Fin N => (1 : ℝ)) = 1 from Matrix.diagonal_one, Matrix.mul_one,
      self_mul_star']
  | succ m ih =>
    rw [pow_succ, ih]
    refine (congrArg (fun X => (hB.eigenvectorUnitary : Mat N) *
      diagonal (fun i => hB.eigenvalues i ^ m) * star (hB.eigenvectorUnitary : Mat N) * X)
      (eq_conj B hB)).trans ?_
    have : (hB.eigenvectorUnitary : Mat N) * diagonal (fun i => hB.eigenvalues i ^ m) *
        star (hB.eigenvectorUnitary : Mat N) * ((hB.eigenvectorUnitary : Mat N) *
        diagonal hB.eigenvalues * star (hB.eigenvectorUnitary : Mat N)) =
        (hB.eigenvectorUnitary : Mat N) * (diagonal (fun i => hB.eigenvalues i ^ m) *
        (star (hB.eigenvectorUnitary : Mat N) * (hB.eigenvectorUnitary : Mat N)) *
        diagonal hB.eigenvalues) * star (hB.eigenvectorUnitary : Mat N) := by
      simp only [Matrix.mul_assoc]
    rw [this, star_mul_self', Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    simp only [pow_succ]

/-- `(1 + c B)ᵐ` in the eigenbasis of `B`. -/
theorem one_add_smul_pow_eq_conj {N : ℕ} (B : Mat N) (hB : B.IsHermitian) (c : ℝ) (m : ℕ) :
    (1 + c • B) ^ m = (hB.eigenvectorUnitary : Mat N) *
      diagonal (fun i => (1 + c * hB.eigenvalues i) ^ m) *
      star (hB.eigenvectorUnitary : Mat N) := by
  have h1 : (1 + c • B) = (hB.eigenvectorUnitary : Mat N) *
      diagonal (fun i => 1 + c * hB.eigenvalues i) * star (hB.eigenvectorUnitary : Mat N) := by
    have hd : diagonal (fun i => 1 + c * hB.eigenvalues i) =
        (1 : Mat N) + c • diagonal hB.eigenvalues := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, self_mul_star', Matrix.mul_smul,
      Matrix.smul_mul, ← eq_conj B hB]
  induction m with
  | zero =>
    simp only [pow_zero]
    rw [show (diagonal fun _ : Fin N => (1 : ℝ)) = 1 from Matrix.diagonal_one, Matrix.mul_one,
      self_mul_star']
  | succ m ih =>
    rw [pow_succ, ih]
    refine (congrArg (fun X => (hB.eigenvectorUnitary : Mat N) *
      diagonal (fun i => (1 + c * hB.eigenvalues i) ^ m) *
      star (hB.eigenvectorUnitary : Mat N) * X) h1).trans ?_
    have : (hB.eigenvectorUnitary : Mat N) * diagonal (fun i => (1 + c * hB.eigenvalues i) ^ m) *
        star (hB.eigenvectorUnitary : Mat N) * ((hB.eigenvectorUnitary : Mat N) *
        diagonal (fun i => 1 + c * hB.eigenvalues i) * star (hB.eigenvectorUnitary : Mat N)) =
        (hB.eigenvectorUnitary : Mat N) * (diagonal (fun i => (1 + c * hB.eigenvalues i) ^ m) *
        (star (hB.eigenvectorUnitary : Mat N) * (hB.eigenvectorUnitary : Mat N)) *
        diagonal (fun i => 1 + c * hB.eigenvalues i)) * star (hB.eigenvectorUnitary : Mat N) := by
      simp only [Matrix.mul_assoc]
    rw [this, star_mul_self', Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    simp only [pow_succ]

/-- Trace against a conjugated diagonal matrix. -/
theorem trace_mul_conj {N : ℕ} (U V : Mat N) (d : Fin N → ℝ) :
    Matrix.trace (V * (U * diagonal d * star U)) = ∑ i, (star U * V * U) i i * d i := by
  have : V * (U * diagonal d * star U) = (V * U * diagonal d) * star U := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.mul_diagonal]

/-- A trace of a conjugated diagonal matrix. -/
theorem trace_conj {N : ℕ} (B : Mat N) (hB : B.IsHermitian) (d : Fin N → ℝ) :
    Matrix.trace ((hB.eigenvectorUnitary : Mat N) * diagonal d *
      star (hB.eigenvectorUnitary : Mat N)) = ∑ i, d i := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_mul_self', Matrix.one_mul,
    Matrix.trace_diagonal]

/-- `tr (1 + c B)ᵐ = ∑ᵢ (1 + c λᵢ)ᵐ`. -/
theorem trace_one_add_smul_pow {N : ℕ} (B : Mat N) (hB : B.IsHermitian) (c : ℝ) (m : ℕ) :
    Matrix.trace ((1 + c • B) ^ m) = ∑ i, (1 + c * hB.eigenvalues i) ^ m := by
  rw [one_add_smul_pow_eq_conj B hB, trace_conj]

/-- `Fn` in terms of the eigenvalues of `M`. -/
theorem Fn_eq_sum {N : ℕ} (θ : ℝ) (n : ℕ) (M : Mat N) (hM : M.IsHermitian) :
    Fn θ n M = ∑ i, (1 + θ / (n : ℝ) * hM.eigenvalues i) ^ n :=
  trace_one_add_smul_pow M hM _ n

/-- A diagonal entry is bounded by the operator norm. -/
theorem abs_apply_le_norm {N : ℕ} (A : Mat N) (i j : Fin N) : |A i j| ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℝ))
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin N) ℝ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℝ)))) i
  refine le_trans (le_of_eq ?_) h2
  rw [Real.norm_eq_abs]
  congr 1
  simp

theorem norm_conj {N : ℕ} (B : Mat N) (hB : B.IsHermitian) (V : Mat N) :
    ‖star (hB.eigenvectorUnitary : Mat N) * V * (hB.eigenvectorUnitary : Mat N)‖ = ‖V‖ := by
  rw [CStarRing.norm_mul_coe_unitary, ← Unitary.coe_star, CStarRing.norm_coe_unitary_mul]

theorem norm_eq_norm_eigenvalues {N : ℕ} (B : Mat N) (hB : B.IsHermitian) :
    ‖B‖ = ‖hB.eigenvalues‖ := by
  conv_lhs => rw [eq_conj B hB]
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

theorem trace_pow_eq_sum {N : ℕ} (B : Mat N) (hB : B.IsHermitian) (m : ℕ) :
    Matrix.trace (B ^ m) = ∑ i, hB.eigenvalues i ^ m := by
  rw [pow_eq_conj B hB, trace_conj]

end StrongConv.T38.PartL
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part L: spectral toolkit for real symmetric matrices -/
alias trace_pow_eq_sum := StrongConv.T38.PartL.trace_pow_eq_sum

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartL
theorem abs_eigenvalues_le_norm {N : ℕ} (B : Mat N) (hB : B.IsHermitian) (i : Fin N) :
    |hB.eigenvalues i| ≤ ‖B‖ := by
  rw [norm_eq_norm_eigenvalues B hB, ← Real.norm_eq_abs]
  exact norm_le_pi_norm _ i

end StrongConv.T38.PartL
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartL
theorem exists_abs_eigenvalues_eq_norm {N : ℕ} (hN : 1 ≤ N) (B : Mat N) (hB : B.IsHermitian) :
    ∃ i, |hB.eigenvalues i| = ‖B‖ := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |hB.eigenvalues i|) hne
  refine ⟨i, le_antisymm (abs_eigenvalues_le_norm B hB i) ?_⟩
  rw [norm_eq_norm_eigenvalues B hB]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact hi j (Finset.mem_univ _)

end StrongConv.T38.PartL
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartL
theorem abs_trace_mul_pow_le {N : ℕ} (B V : Mat N) (hB : B.IsHermitian) (a : ℕ) :
    |Matrix.trace (V * B ^ a)| ≤ ‖V‖ * ∑ i, |hB.eigenvalues i| ^ a := by
  rw [pow_eq_conj B hB, trace_mul_conj, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact (abs_apply_le_norm _ i i).trans (norm_conj B hB V).le

end StrongConv.T38.PartL
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias abs_trace_mul_pow_le := StrongConv.T38.PartL.abs_trace_mul_pow_le

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartL
theorem Fn_nonneg {N : ℕ} (θ : ℝ) (n : ℕ) (hn : Even n) (M : Mat N) (hM : M.IsHermitian) :
    0 ≤ Fn θ n M := by
  rw [Fn_eq_sum θ n M hM]
  exact Finset.sum_nonneg fun i _ => hn.pow_nonneg _

end StrongConv.T38.PartL
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias Fn_nonneg := StrongConv.T38.PartL.Fn_nonneg

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartL
theorem Fn_le_exp {N : ℕ} (θ : ℝ) (n : ℕ) (hn : 1 ≤ n) (M : Mat N) (hM : M.IsHermitian) :
    Fn θ n M ≤ N * Real.exp (|θ| * ‖M‖) := by
  rw [Fn_eq_sum θ n M hM]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ i, (1 + θ / (n : ℝ) * hM.eigenvalues i) ^ n ≤ Real.exp (|θ| * ‖M‖) := by
    intro i
    have h1 : |1 + θ / (n : ℝ) * hM.eigenvalues i| ≤ 1 + |θ| * ‖M‖ / n := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one, abs_mul, abs_div, abs_of_pos hn0, div_mul_eq_mul_div]
      gcongr
      exact abs_eigenvalues_le_norm M hM i
    have h2 : 1 + |θ| * ‖M‖ / n ≤ Real.exp (|θ| * ‖M‖ / n) := by
      linarith [Real.add_one_le_exp (|θ| * ‖M‖ / n)]
    calc (1 + θ / (n : ℝ) * hM.eigenvalues i) ^ n
        ≤ |1 + θ / (n : ℝ) * hM.eigenvalues i| ^ n := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (Real.exp (|θ| * ‖M‖ / n)) ^ n :=
          pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) n
      _ = Real.exp (|θ| * ‖M‖) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  calc ∑ i, (1 + θ / (n : ℝ) * hM.eigenvalues i) ^ n
      ≤ ∑ _i : Fin N, Real.exp (|θ| * ‖M‖) := Finset.sum_le_sum fun i _ => key i
    _ = N * Real.exp (|θ| * ‖M‖) := by simp

end StrongConv.T38.PartL
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias Fn_le_exp := StrongConv.T38.PartL.Fn_le_exp

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartL
theorem pow_le_Fn_add_Fn_neg {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ) (hn : Even n)
    (hn1 : 1 ≤ n) (M : Mat N) (hM : M.IsHermitian) :
    (1 + θ * ‖M‖ / n) ^ n ≤ Fn θ n M + Fn (-θ) n M := by
  obtain ⟨i, hi⟩ := exists_abs_eigenvalues_eq_norm hN M hM
  have hpos : ∀ (θ' : ℝ) (j : Fin N), 0 ≤ (1 + θ' / (n : ℝ) * hM.eigenvalues j) ^ n :=
    fun θ' j => hn.pow_nonneg _
  have single : ∀ θ' : ℝ, (1 + θ' / (n : ℝ) * hM.eigenvalues i) ^ n ≤ Fn θ' n M := by
    intro θ'
    rw [Fn_eq_sum θ' n M hM]
    exact Finset.single_le_sum (f := fun j => (1 + θ' / (n : ℝ) * hM.eigenvalues j) ^ n)
      (fun j _ => hpos θ' j) (Finset.mem_univ i)
  rcases abs_choice (hM.eigenvalues i) with h | h
  · have e : (1 + θ * ‖M‖ / n) ^ n = (1 + θ / (n : ℝ) * hM.eigenvalues i) ^ n := by
      rw [← hi, h]; ring
    rw [e]
    linarith [single θ, Fn_nonneg (-θ) n hn M hM]
  · have e : (1 + θ * ‖M‖ / n) ^ n = (1 + (-θ) / (n : ℝ) * hM.eigenvalues i) ^ n := by
      rw [← hi, h]; ring
    rw [e]
    linarith [single (-θ), Fn_nonneg θ n hn M hM]

end StrongConv.T38.PartL
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias pow_le_Fn_add_Fn_neg := StrongConv.T38.PartL.pow_le_Fn_add_Fn_neg

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartA
/-!
# T38, Part A: the three-fold trace Hölder inequality

`|tr(V₁ Bᵃ V₂ Bᵇ V₃ Bᶜ)| ≤ ‖V₁‖‖V₂‖‖V₃‖ ∑ᵢ |λᵢ|^(a+b+c)` for a real symmetric `B`, by complex
interpolation (Hadamard three lines, twice) in the eigenbasis of `B`.
-/
/-! ## Operator-norm facts -/
theorem norm_entry_le {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜)
    (i j : Fin N) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : 𝕜))
  have h1 : ‖(EuclideanSpace.single j (1 : 𝕜) : EuclideanSpace 𝕜 (Fin N))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le
    ((EuclideanSpace.equiv (Fin N) 𝕜).symm (M *ᵥ (EuclideanSpace.single j (1 : 𝕜)))) i
  simpa using h2

theorem norm_trace_mul_diagonal_le {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) 𝕜) (d : Fin N → 𝕜) :
    ‖Matrix.trace (M * Matrix.diagonal d)‖ ≤ ‖M‖ * ∑ i, ‖d i‖ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  calc ‖∑ i, M i i * d i‖ ≤ ∑ i, ‖M i i * d i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖M‖ * ‖d i‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        gcongr
        exact norm_entry_le M i i
    _ = _ := by rw [Finset.mul_sum]

theorem norm_diagonal_le {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} (d : Fin N → 𝕜) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ i, ‖d i‖ ≤ R) : ‖(Matrix.diagonal d : Matrix (Fin N) (Fin N) 𝕜)‖ ≤ R := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hR).2 h

theorem norm_five {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} (A₁ E₁ A₂ E₂ A₃ : Matrix (Fin N) (Fin N) 𝕜)
    (e₁ e₂ : ℝ) (h₁ : ‖E₁‖ ≤ e₁) (h₂ : ‖E₂‖ ≤ e₂) :
    ‖A₁ * E₁ * A₂ * E₂ * A₃‖ ≤ ‖A₁‖ * e₁ * ‖A₂‖ * e₂ * ‖A₃‖ := by
  have he₁ : 0 ≤ e₁ := (norm_nonneg _).trans h₁
  have h1 : ‖A₁ * E₁‖ ≤ ‖A₁‖ * e₁ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
  have h2 : ‖A₁ * E₁ * A₂‖ ≤ ‖A₁‖ * e₁ * ‖A₂‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  have h3 : ‖A₁ * E₁ * A₂ * E₂‖ ≤ ‖A₁‖ * e₁ * ‖A₂‖ * e₂ :=
    (norm_mul_le _ _).trans (mul_le_mul h2 h₂ (norm_nonneg _) (by positivity))
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))

/-- A real matrix does not gain norm when read as a complex matrix. -/
theorem norm_map_ofReal_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ‖(Complex.ofRealHom.mapMatrix A : Matrix (Fin N) (Fin N) ℂ)‖ ≤ ‖A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℂ)]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  let u : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun i => (x i).re
  let v : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun i => (x i).im
  have hu := A.l2_opNorm_mulVec u
  have hv := A.l2_opNorm_mulVec v
  have hu2 : ‖(EuclideanSpace.equiv (Fin N) ℝ).symm (A *ᵥ u)‖ ^ 2 ≤ (‖A‖ * ‖u‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hv2 : ‖(EuclideanSpace.equiv (Fin N) ℝ).symm (A *ᵥ v)‖ ^ 2 ≤ (‖A‖ * ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hv 2
  have hx : ‖x‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, u, v, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  have hT : ‖toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (Complex.ofRealHom.mapMatrix A) x‖ ^ 2 =
      ‖(EuclideanSpace.equiv (Fin N) ℝ).symm (A *ᵥ u)‖ ^ 2 +
        ‖(EuclideanSpace.equiv (Fin N) ℝ).symm (A *ᵥ v)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, ofLp_toEuclideanCLM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq, Matrix.mulVec, dotProduct, u, v]
  rw [hT, mul_pow, hx]
  nlinarith [hu2, hv2]

/-! ## The strip maximum principle -/
theorem strip_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (K C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ K)
    (h0 : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ C) (h1 : ∀ z : ℂ, z.re = 1 → ‖f z‖ ≤ C)
    (z : ℂ) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) : ‖f z‖ ≤ C := by
  have hB : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hK w hw.1 hw.2
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' f
    (z := z) (a := C) (b := C) ⟨hz0, hz1⟩ hf.diffContOnCl hB
    (fun w hw => h0 w hw) (fun w hw => h1 w hw)
  rwa [← Real.rpow_add' hC (by simp), sub_add_cancel, Real.rpow_one] at h

/-! ## The interpolated trace -/
/-- `diag(exp(ζ ℓᵢ))`. -/
def E {N : ℕ} (ℓ : Fin N → ℝ) (ζ : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => Complex.exp (ζ * ℓ i)

/-- `tr(A₁ ρ^ζ₁ A₂ ρ^ζ₂ A₃ ρ^ζ₃)` with `ρᵢ = exp ℓᵢ`. -/
def G {N : ℕ} (A₁ A₂ A₃ : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ) (ζ₁ ζ₂ ζ₃ : ℂ) : ℂ :=
  Matrix.trace (A₁ * E ℓ ζ₁ * A₂ * E ℓ ζ₂ * A₃ * E ℓ ζ₃)

theorem norm_exp_mul {N : ℕ} (ℓ : Fin N → ℝ) (ζ : ℂ) (i : Fin N) :
    ‖Complex.exp (ζ * ℓ i)‖ = Real.exp (ζ.re * ℓ i) := by
  simp [Complex.norm_exp]

theorem norm_E_le_one {N : ℕ} (ℓ : Fin N → ℝ) (ζ : ℂ) (h : ζ.re = 0) : ‖E ℓ ζ‖ ≤ 1 :=
  norm_diagonal_le _ 1 zero_le_one fun i => by rw [norm_exp_mul, h]; simp

theorem norm_exp_mul_le {N : ℕ} (ℓ : Fin N → ℝ) (ζ : ℂ) (R : ℝ) (hR : |ζ.re| ≤ R) (i : Fin N) :
    ‖Complex.exp (ζ * ℓ i)‖ ≤ Real.exp (R * ∑ j, |ℓ j|) := by
  rw [norm_exp_mul]
  apply Real.exp_le_exp.2
  have h1 : |ℓ i| ≤ ∑ j, |ℓ j| :=
    Finset.single_le_sum (f := fun j => |ℓ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  calc ζ.re * ℓ i ≤ |ζ.re * ℓ i| := le_abs_self _
    _ = |ζ.re| * |ℓ i| := abs_mul _ _
    _ ≤ R * ∑ j, |ℓ j| := mul_le_mul hR h1 (abs_nonneg _) ((abs_nonneg _).trans hR)

theorem G_vertex {N : ℕ} (A₁ A₂ A₃ : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ) (ζ₁ ζ₂ ζ₃ : ℂ)
    (h₁ : ζ₁.re = 0) (h₂ : ζ₂.re = 0) (h₃ : ζ₃.re = 1) :
    ‖G A₁ A₂ A₃ ℓ ζ₁ ζ₂ ζ₃‖ ≤ ‖A₁‖ * ‖A₂‖ * ‖A₃‖ * ∑ i, Real.exp (ℓ i) := by
  unfold G
  refine (norm_trace_mul_diagonal_le _ _).trans ?_
  have e3 : ∑ i, ‖Complex.exp (ζ₃ * ℓ i)‖ = ∑ i, Real.exp (ℓ i) :=
    Finset.sum_congr rfl fun i _ => by rw [norm_exp_mul, h₃, one_mul]
  rw [e3]
  have h5 := norm_five A₁ (E ℓ ζ₁) A₂ (E ℓ ζ₂) A₃ 1 1 (norm_E_le_one ℓ ζ₁ h₁)
    (norm_E_le_one ℓ ζ₂ h₂)
  simp only [mul_one] at h5
  exact mul_le_mul_of_nonneg_right h5 (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le)

theorem G_cyclic {N : ℕ} (A₁ A₂ A₃ : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ) (ζ₁ ζ₂ ζ₃ : ℂ) :
    G A₁ A₂ A₃ ℓ ζ₁ ζ₂ ζ₃ = G A₂ A₃ A₁ ℓ ζ₂ ζ₃ ζ₁ := by
  unfold G
  rw [show A₁ * E ℓ ζ₁ * A₂ * E ℓ ζ₂ * A₃ * E ℓ ζ₃ =
      (A₁ * E ℓ ζ₁) * (A₂ * E ℓ ζ₂ * A₃ * E ℓ ζ₃) by simp only [mul_assoc], Matrix.trace_mul_comm]
  simp only [mul_assoc]

theorem G_bound {N : ℕ} (A₁ A₂ A₃ : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ) (ζ₁ ζ₂ ζ₃ : ℂ)
    (R : ℝ) (h₁ : |ζ₁.re| ≤ R) (h₂ : |ζ₂.re| ≤ R) (h₃ : |ζ₃.re| ≤ R) :
    ‖G A₁ A₂ A₃ ℓ ζ₁ ζ₂ ζ₃‖ ≤
      ‖A₁‖ * Real.exp (R * ∑ j, |ℓ j|) * ‖A₂‖ * Real.exp (R * ∑ j, |ℓ j|) * ‖A₃‖ *
        ∑ _i : Fin N, Real.exp (R * ∑ j, |ℓ j|) := by
  unfold G
  refine (norm_trace_mul_diagonal_le _ _).trans ?_
  have h5 := norm_five A₁ (E ℓ ζ₁) A₂ (E ℓ ζ₂) A₃ _ _
    (norm_diagonal_le _ _ (Real.exp_pos _).le (norm_exp_mul_le ℓ ζ₁ R h₁))
    (norm_diagonal_le _ _ (Real.exp_pos _).le (norm_exp_mul_le ℓ ζ₂ R h₂))
  exact mul_le_mul h5 (Finset.sum_le_sum fun i _ => norm_exp_mul_le ℓ ζ₃ R h₃ i)
    (Finset.sum_nonneg fun i _ => norm_nonneg _) (by positivity)

theorem G_eq_sum {N : ℕ} (A₁ A₂ A₃ : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ) (ζ₁ ζ₂ ζ₃ : ℂ) :
    G A₁ A₂ A₃ ℓ ζ₁ ζ₂ ζ₃ = ∑ k, (∑ j, (∑ i, A₁ k i * Complex.exp (ζ₁ * ℓ i) * A₂ i j) *
      Complex.exp (ζ₂ * ℓ j) * A₃ j k) * Complex.exp (ζ₃ * ℓ k) := by
  unfold G E
  simp only [Matrix.trace, Matrix.diag_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem G_differentiable {N : ℕ} (A₁ A₂ A₃ : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (g₁ g₂ g₃ : ℂ → ℂ) (h₁ : Differentiable ℂ g₁) (h₂ : Differentiable ℂ g₂)
    (h₃ : Differentiable ℂ g₃) :
    Differentiable ℂ fun z => G A₁ A₂ A₃ ℓ (g₁ z) (g₂ z) (g₃ z) := by
  simp only [G_eq_sum]
  fun_prop

/-- Edge of the simplex: `Re ζ₃ = 0`, `Re ζ₁ + Re ζ₂ = 1`. -/
theorem G_edge {N : ℕ} (A₁ A₂ A₃ : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ) (ζ₁ ζ₂ ζ₃ : ℂ)
    (h₁ : 0 ≤ ζ₁.re) (h₂ : 0 ≤ ζ₂.re) (h₁₂ : ζ₁.re + ζ₂.re = 1) (h₃ : ζ₃.re = 0) :
    ‖G A₁ A₂ A₃ ℓ ζ₁ ζ₂ ζ₃‖ ≤ ‖A₁‖ * ‖A₂‖ * ‖A₃‖ * ∑ i, Real.exp (ℓ i) := by
  have key := strip_bound (fun z => G A₁ A₂ A₃ ℓ z (ζ₁ + ζ₂ - z) ζ₃)
    (G_differentiable A₁ A₂ A₃ ℓ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
    (‖A₁‖ * Real.exp (1 * ∑ j, |ℓ j|) * ‖A₂‖ * Real.exp (1 * ∑ j, |ℓ j|) * ‖A₃‖ *
        ∑ _i : Fin N, Real.exp (1 * ∑ j, |ℓ j|))
    (‖A₁‖ * ‖A₂‖ * ‖A₃‖ * ∑ i, Real.exp (ℓ i)) (by positivity) ?_ ?_ ?_ ζ₁ h₁ (by linarith)
  · simpa using key
  · intro z hz0 hz1
    refine G_bound A₁ A₂ A₃ ℓ _ _ _ 1 ?_ ?_ ?_
    · rw [abs_le]; constructor <;> linarith
    · simp only [Complex.sub_re, Complex.add_re, h₁₂]
      rw [abs_le]; constructor <;> linarith
    · simp [h₃]
  · intro z hz
    rw [G_cyclic, G_cyclic]
    have := G_vertex A₃ A₁ A₂ ℓ ζ₃ z (ζ₁ + ζ₂ - z) h₃ hz (by
      simp only [Complex.sub_re, Complex.add_re, h₁₂, hz]; norm_num)
    exact this.trans (le_of_eq (by ring))
  · intro z hz
    rw [G_cyclic]
    have := G_vertex A₂ A₃ A₁ ℓ (ζ₁ + ζ₂ - z) ζ₃ z (by
      simp only [Complex.sub_re, Complex.add_re, h₁₂, hz]; norm_num) h₃ hz
    exact this.trans (le_of_eq (by ring))

/-- The whole simplex, real exponents. -/
theorem G_simplex {N : ℕ} (A₁ A₂ A₃ : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ) (t₁ t₂ t₃ : ℝ)
    (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃) (hs : t₁ + t₂ + t₃ = 1) :
    ‖G A₁ A₂ A₃ ℓ t₁ t₂ t₃‖ ≤ ‖A₁‖ * ‖A₂‖ * ‖A₃‖ * ∑ i, Real.exp (ℓ i) := by
  rcases eq_or_lt_of_le (show t₃ ≤ 1 by linarith) with h | h
  · have ht1 : t₁ = 0 := by linarith
    have ht2 : t₂ = 0 := by linarith
    exact G_vertex _ _ _ ℓ _ _ _ (by simp [ht1]) (by simp [ht2]) (by simp [h])
  · have hs0 : 0 < 1 - t₃ := by linarith
    have ha0 : 0 ≤ t₁ / (1 - t₃) := div_nonneg h₁ hs0.le
    have hb0 : 0 ≤ t₂ / (1 - t₃) := div_nonneg h₂ hs0.le
    have hab : t₁ / (1 - t₃) + t₂ / (1 - t₃) = 1 := by
      rw [← add_div, div_eq_one_iff_eq hs0.ne']; linarith
    have ea : t₁ / (1 - t₃) * (1 - t₃) = t₁ := div_mul_cancel₀ t₁ hs0.ne'
    have eb : t₂ / (1 - t₃) * (1 - t₃) = t₂ := div_mul_cancel₀ t₂ hs0.ne'
    generalize t₁ / (1 - t₃) = α at ha0 hab ea
    generalize t₂ / (1 - t₃) = β at hb0 hab eb
    have key := strip_bound
      (fun z => G A₁ A₂ A₃ ℓ ((α : ℂ) * (1 - z)) ((β : ℂ) * (1 - z)) z)
      (G_differentiable A₁ A₂ A₃ ℓ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
      (‖A₁‖ * Real.exp (1 * ∑ j, |ℓ j|) * ‖A₂‖ * Real.exp (1 * ∑ j, |ℓ j|) * ‖A₃‖ *
        ∑ _i : Fin N, Real.exp (1 * ∑ j, |ℓ j|))
      (‖A₁‖ * ‖A₂‖ * ‖A₃‖ * ∑ i, Real.exp (ℓ i)) (by positivity) ?_ ?_ ?_ (t₃ : ℂ)
      (by simpa using h₃) (by simpa using h.le)
    · have e1 : (α : ℂ) * (1 - (t₃ : ℂ)) = (t₁ : ℂ) := by
        rw [← ea]; push_cast; ring
      have e2 : (β : ℂ) * (1 - (t₃ : ℂ)) = (t₂ : ℂ) := by
        rw [← eb]; push_cast; ring
      simpa only [e1, e2] using key
    · intro z hz0 hz1
      refine G_bound A₁ A₂ A₃ ℓ _ _ _ 1 ?_ ?_ ?_
      · simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
        rw [abs_le]; constructor <;> nlinarith
      · simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
        rw [abs_le]; constructor <;> nlinarith
      · rw [abs_le]; constructor <;> linarith
    · intro z hz
      exact G_edge A₁ A₂ A₃ ℓ _ _ _
        (by simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, hz]; linarith)
        (by simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, hz]; linarith)
        (by simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, hz]; linarith) hz
    · intro z hz
      exact G_vertex A₁ A₂ A₃ ℓ _ _ _
        (by simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, hz]; ring)
        (by simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, hz]; ring) hz

/-! ## The real inequality in diagonal form -/
theorem core0 {N : ℕ} (W₁ W₂ W₃ : Matrix (Fin N) (Fin N) ℝ) (μ : Fin N → ℝ)
    (hμ : ∀ i, 0 < μ i) (a b c : ℕ) :
    |Matrix.trace (W₁ * Matrix.diagonal (fun i => μ i ^ a) * W₂ *
        Matrix.diagonal (fun i => μ i ^ b) * W₃ * Matrix.diagonal (fun i => μ i ^ c))| ≤
      ‖W₁‖ * ‖W₂‖ * ‖W₃‖ * ∑ i, μ i ^ (a + b + c) := by
  rcases Nat.eq_zero_or_pos (a + b + c) with h0 | hm
  · obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ c = 0 := by omega
    have h := norm_trace_mul_diagonal_le
      (W₁ * Matrix.diagonal (fun i => μ i ^ 0) * W₂ * Matrix.diagonal (fun i => μ i ^ 0) * W₃)
      (fun i => μ i ^ 0)
    have h5 := norm_five W₁ (Matrix.diagonal (fun i => μ i ^ 0)) W₂
      (Matrix.diagonal (fun i => μ i ^ 0)) W₃ 1 1
      (norm_diagonal_le _ 1 zero_le_one (by simp)) (norm_diagonal_le _ 1 zero_le_one (by simp))
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    simp only [mul_one] at h5
    exact mul_le_mul h5 (le_of_eq (by simp)) (Finset.sum_nonneg fun i _ => norm_nonneg _)
      (by positivity)
  · have hm' : ((a + b + c : ℕ) : ℝ) ≠ 0 := by positivity
    set m : ℕ := a + b + c with hmdef
    let ℓ : Fin N → ℝ := fun i => (m : ℝ) * Real.log (μ i)
    let φ := (Complex.ofRealHom.mapMatrix : Matrix (Fin N) (Fin N) ℝ →+* Matrix (Fin N) (Fin N) ℂ)
    have hE : ∀ k : ℕ, E ℓ (((k : ℝ) / (m : ℝ) : ℝ) : ℂ) =
        φ (Matrix.diagonal fun i => μ i ^ k) := by
      intro k
      unfold E
      rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      simp only [Complex.ofRealHom_eq_coe]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
      congr 1
      rw [show (k : ℝ) / (m : ℝ) * ((m : ℝ) * Real.log (μ i)) = k * Real.log (μ i) by
        field_simp, Real.exp_nat_mul, Real.exp_log (hμ i)]
    have hG : ((Matrix.trace (W₁ * Matrix.diagonal (fun i => μ i ^ a) * W₂ *
        Matrix.diagonal (fun i => μ i ^ b) * W₃ * Matrix.diagonal (fun i => μ i ^ c)) : ℝ) : ℂ) =
        G (φ W₁) (φ W₂) (φ W₃) ℓ (((a : ℝ) / (m : ℝ) : ℝ) : ℂ) (((b : ℝ) / (m : ℝ) : ℝ) : ℂ)
          (((c : ℝ) / (m : ℝ) : ℝ) : ℂ) := by
      unfold G
      rw [hE a, hE b, hE c]
      simp only [← map_mul]
      exact AddMonoidHom.map_trace Complex.ofRealHom _
    have hsum : (a : ℝ) / m + (b : ℝ) / m + (c : ℝ) / m = 1 := by
      rw [← add_div, ← add_div, div_eq_one_iff_eq hm', hmdef]; push_cast; ring
    have hGle := G_simplex (φ W₁) (φ W₂) (φ W₃) ℓ _ _ _
      (by positivity : (0 : ℝ) ≤ (a : ℝ) / m) (by positivity : (0 : ℝ) ≤ (b : ℝ) / m)
      (by positivity : (0 : ℝ) ≤ (c : ℝ) / m) hsum
    rw [← hG, Complex.norm_real, Real.norm_eq_abs] at hGle
    refine hGle.trans ?_
    have hexp : ∀ i, Real.exp (ℓ i) = μ i ^ m := fun i => by
      simp only [ℓ]; rw [Real.exp_nat_mul, Real.exp_log (hμ i)]
    simp only [hexp]
    have hS : 0 ≤ ∑ i, μ i ^ m := Finset.sum_nonneg fun i _ => pow_nonneg (hμ i).le _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul (norm_map_ofReal_le W₁) (norm_map_ofReal_le W₂) (norm_nonneg _)
        (norm_nonneg _)) (norm_map_ofReal_le W₃) (norm_nonneg _) (by positivity)) hS

theorem core {N : ℕ} (W₁ W₂ W₃ : Matrix (Fin N) (Fin N) ℝ) (μ : Fin N → ℝ)
    (hμ : ∀ i, 0 < μ i) (σ₁ σ₂ σ₃ : Fin N → ℝ) (h₁ : ∀ i, |σ₁ i| ≤ 1) (h₂ : ∀ i, |σ₂ i| ≤ 1)
    (h₃ : ∀ i, |σ₃ i| ≤ 1) (a b c : ℕ) :
    |Matrix.trace (W₁ * Matrix.diagonal (fun i => σ₁ i * μ i ^ a) * W₂ *
        Matrix.diagonal (fun i => σ₂ i * μ i ^ b) * W₃ *
        Matrix.diagonal (fun i => σ₃ i * μ i ^ c))| ≤
      ‖W₁‖ * ‖W₂‖ * ‖W₃‖ * ∑ i, μ i ^ (a + b + c) := by
  have hd : ∀ (σ : Fin N → ℝ) (k : ℕ), Matrix.diagonal (fun i => σ i * μ i ^ k) =
      Matrix.diagonal σ * Matrix.diagonal (fun i => μ i ^ k) := fun σ k => by
    rw [Matrix.diagonal_mul_diagonal]
  have hn : ∀ (W : Matrix (Fin N) (Fin N) ℝ) (σ : Fin N → ℝ), (∀ i, |σ i| ≤ 1) →
      ‖W * Matrix.diagonal σ‖ ≤ ‖W‖ := fun W σ h => by
    refine (norm_mul_le _ _).trans ?_
    have := norm_diagonal_le σ 1 zero_le_one h
    nlinarith [norm_nonneg W]
  rw [hd, hd, hd]
  rw [show W₁ * (Matrix.diagonal σ₁ * Matrix.diagonal (fun i => μ i ^ a)) * W₂ *
      (Matrix.diagonal σ₂ * Matrix.diagonal (fun i => μ i ^ b)) * W₃ *
      (Matrix.diagonal σ₃ * Matrix.diagonal (fun i => μ i ^ c)) =
      (W₁ * Matrix.diagonal σ₁) * Matrix.diagonal (fun i => μ i ^ a) *
      (W₂ * Matrix.diagonal σ₂) * Matrix.diagonal (fun i => μ i ^ b) *
      (W₃ * Matrix.diagonal σ₃) * Matrix.diagonal (fun i => μ i ^ c) by simp only [mul_assoc]]
  refine (core0 _ _ _ μ hμ a b c).trans ?_
  have hS : 0 ≤ ∑ i, μ i ^ (a + b + c) := Finset.sum_nonneg fun i _ => pow_nonneg (hμ i).le _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul (hn W₁ σ₁ h₁) (hn W₂ σ₂ h₂) (norm_nonneg _)
      (norm_nonneg _)) (hn W₃ σ₃ h₃) (norm_nonneg _) (by positivity)) hS

theorem norm_le_one_of_star_mul_self {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ)
    (h : star U * U = 1) : ‖U‖ ≤ 1 := by
  have h1 : ‖U‖ * ‖U‖ = ‖(1 : Matrix (Fin N) (Fin N) ℝ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.star_eq_conjTranspose, h]
  have h2 : ‖(1 : Matrix (Fin N) (Fin N) ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one]
    exact norm_diagonal_le _ 1 zero_le_one (by simp)
  nlinarith [norm_nonneg U]

/-! ## The stub -/
/-- `|tr(V₁ Bᵃ V₂ Bᵇ V₃ Bᶜ)| ≤ ‖V₁‖‖V₂‖‖V₃‖ · tr |B|^(a+b+c)` for real symmetric `B`. -/
theorem abs_trace_three_le {N : ℕ} (B V₁ V₂ V₃ : Mat N) (hB : B.IsHermitian) (a b c : ℕ) :
    |Matrix.trace (V₁ * B ^ a * V₂ * B ^ b * V₃ * B ^ c)| ≤
      ‖V₁‖ * ‖V₂‖ * ‖V₃‖ * ∑ i, |hB.eigenvalues i| ^ (a + b + c) := by
  obtain ⟨U, lam, hU1, hU2, hpow, hlam⟩ : ∃ (U : Mat N) (lam : Fin N → ℝ),
      star U * U = 1 ∧ U * star U = 1 ∧
      (∀ k : ℕ, B ^ k = U * Matrix.diagonal (fun i => lam i ^ k) * star U) ∧
      lam = hB.eigenvalues := by
    refine ⟨(hB.eigenvectorUnitary : Mat N), hB.eigenvalues, Unitary.coe_star_mul_self _,
      Unitary.coe_mul_star_self _, fun k => ?_, rfl⟩
    calc B ^ k = (Unitary.conjStarAlgAut ℝ _ hB.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues))) ^ k :=
          congrArg (fun X => X ^ k) hB.spectral_theorem
      _ = _ := by
          rw [← map_pow, Matrix.diagonal_pow, Unitary.conjStarAlgAut_apply]
          rfl
  rw [← hlam]
  clear hlam
  have hUn : ‖U‖ ≤ 1 := norm_le_one_of_star_mul_self U hU1
  have hUn' : ‖star U‖ ≤ 1 := norm_le_one_of_star_mul_self (star U) (by rwa [star_star])
  have hW : ∀ V : Mat N, ‖star U * V * U‖ ≤ ‖V‖ := fun V => by
    have h1 : ‖star U * V * U‖ ≤ ‖star U‖ * ‖V‖ * ‖U‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    have h2 : ‖star U‖ * ‖V‖ * ‖U‖ ≤ 1 * ‖V‖ * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hUn' (norm_nonneg _)) hUn (norm_nonneg _)
        (by positivity)
    linarith
  have htr : Matrix.trace (V₁ * B ^ a * V₂ * B ^ b * V₃ * B ^ c) =
      Matrix.trace ((star U * V₁ * U) * Matrix.diagonal (fun i => lam i ^ a) *
        (star U * V₂ * U) * Matrix.diagonal (fun i => lam i ^ b) *
        (star U * V₃ * U) * Matrix.diagonal (fun i => lam i ^ c)) := by
    rw [hpow a, hpow b, hpow c]
    rw [show V₁ * (U * Matrix.diagonal (fun i => lam i ^ a) * star U) * V₂ *
        (U * Matrix.diagonal (fun i => lam i ^ b) * star U) * V₃ *
        (U * Matrix.diagonal (fun i => lam i ^ c) * star U) =
        (V₁ * U * Matrix.diagonal (fun i => lam i ^ a) * star U * V₂ *
        U * Matrix.diagonal (fun i => lam i ^ b) * star U * V₃ *
        U * Matrix.diagonal (fun i => lam i ^ c)) * star U by simp only [mul_assoc],
      Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [htr]
  let σ : Fin N → ℝ := fun i => if lam i < 0 then -1 else 1
  have hσ : ∀ i, σ i * |lam i| = lam i := fun i => by
    simp only [σ]
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.1 h)]; ring
  have hσ1 : ∀ (k : ℕ) (i : Fin N), |σ i ^ k| ≤ 1 := fun k i => by
    rw [abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    simp only [σ]
    split_ifs <;> simp
  let W₁ := star U * V₁ * U
  let W₂ := star U * V₂ * U
  let W₃ := star U * V₃ * U
  let L : ℝ → ℝ := fun ε => |Matrix.trace
    (W₁ * Matrix.diagonal (fun i => σ i ^ a * (|lam i| + ε) ^ a) *
      W₂ * Matrix.diagonal (fun i => σ i ^ b * (|lam i| + ε) ^ b) *
      W₃ * Matrix.diagonal (fun i => σ i ^ c * (|lam i| + ε) ^ c))|
  let R : ℝ → ℝ := fun ε => ‖W₁‖ * ‖W₂‖ * ‖W₃‖ * ∑ i, (|lam i| + ε) ^ (a + b + c)
  have hle : ∀ ε : ℝ, 0 < ε → L ε ≤ R ε := fun ε hε =>
    core W₁ W₂ W₃ (fun i => |lam i| + ε) (fun i => by positivity) _ _ _ (hσ1 a) (hσ1 b) (hσ1 c)
      a b c
  have hD : ∀ k : ℕ, Continuous fun ε : ℝ =>
      (Matrix.diagonal (fun i => σ i ^ k * (|lam i| + ε) ^ k) : Mat N) := fun k =>
    Continuous.matrix_diagonal (by fun_prop)
  have hL : Continuous L :=
    continuous_abs.comp (Continuous.matrix_trace
      (((((continuous_const.matrix_mul (hD a)).matrix_mul continuous_const).matrix_mul
        (hD b)).matrix_mul continuous_const).matrix_mul (hD c)))
  have hR : Continuous R := by fun_prop
  have h0 : L 0 ≤ R 0 :=
    le_of_tendsto_of_tendsto ((hL.tendsto 0).mono_left nhdsWithin_le_nhds)
      ((hR.tendsto 0).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun ε (hε : ε ∈ Set.Ioi (0 : ℝ)) => hle ε hε)
  have hL0 : L 0 = |Matrix.trace (W₁ * Matrix.diagonal (fun i => lam i ^ a) *
      W₂ * Matrix.diagonal (fun i => lam i ^ b) * W₃ * Matrix.diagonal (fun i => lam i ^ c))| := by
    simp only [L, add_zero, ← mul_pow, hσ]
  have hR0 : R 0 = ‖W₁‖ * ‖W₂‖ * ‖W₃‖ * ∑ i, |lam i| ^ (a + b + c) := by
    simp only [R, add_zero]
  rw [hL0, hR0] at h0
  refine h0.trans ?_
  have hS : 0 ≤ ∑ i, |lam i| ^ (a + b + c) :=
    Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul (hW V₁) (hW V₂) (norm_nonneg _) (norm_nonneg _)) (hW V₃)
      (norm_nonneg _) (by positivity)) hS

end StrongConv.T38.PartA
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part A: the three-fold trace Hölder inequality -/
alias abs_trace_three_le := StrongConv.T38.PartA.abs_trace_three_le

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartB
open StrongConv.T38
variable {N : ℕ}
/-!
# T38 Part B: Gronwall bound and second-order Taylor expansion of `M ↦ tr (1 + θ M / n) ^ n`
-/
/-- The line `B + t V`. -/
def Bt (B V : Mat N) (t : ℝ) : Mat N := B + t • V

/-- The derivative of `C ^ k` in the direction `V`. -/
def Dm (C V : Mat N) (k : ℕ) : Mat N := ∑ c ∈ Finset.range k, C ^ c * V * C ^ (k - 1 - c)

theorem hasDerivAt_Bt (B V : Mat N) (t : ℝ) : HasDerivAt (Bt B V) V t := by
  have h : HasDerivAt (fun x : ℝ => B + x • V) ((1 : ℝ) • V) t :=
    ((hasDerivAt_id t).smul_const V).const_add B
  rw [one_smul] at h
  exact h

theorem hasDerivAt_Bt_pow (B V : Mat N) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s => Bt B V s ^ k) (Dm (Bt B V t) V k) t := by
  induction k with
  | zero => simpa [Dm] using hasDerivAt_const t (1 : Mat N)
  | succ k ih =>
    have h := ih.mul (hasDerivAt_Bt B V t)
    have e : Dm (Bt B V t) V (k + 1) = Dm (Bt B V t) V k * Bt B V t + Bt B V t ^ k * V := by
      unfold Dm
      rw [Finset.sum_range_succ, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun c hc => ?_
        have hc' : c < k := Finset.mem_range.mp hc
        have : k + 1 - 1 - c = (k - 1 - c) + 1 := by omega
        rw [this, pow_succ, mul_assoc, mul_assoc, mul_assoc]
      · simp
    rw [e]
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp [pow_succ]

theorem hasDerivAt_trace {f : ℝ → Mat N} {f' : Mat N} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t :=
  ((Matrix.traceLinearMap (Fin N) ℝ ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt t h

theorem trace_Dm (C V : Mat N) (k : ℕ) :
    Matrix.trace (Dm C V (k + 1)) = ((k : ℝ) + 1) * Matrix.trace (V * C ^ k) := by
  unfold Dm
  rw [Matrix.trace_sum]
  have : ∀ c ∈ Finset.range (k + 1),
      Matrix.trace (C ^ c * V * C ^ (k + 1 - 1 - c)) = Matrix.trace (V * C ^ k) := by
    intro c hc
    have hc' : c < k + 1 := Finset.mem_range.mp hc
    rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc, ← pow_add]
    congr 3
    omega
  rw [Finset.sum_congr rfl this]
  simp

/-- First derivative. -/
def g1 (B V : Mat N) (m : ℕ) (t : ℝ) : ℝ :=
  ((m : ℝ) + 2) * Matrix.trace (V * Bt B V t ^ (m + 1))

/-- Second derivative. -/
def g2 (B V : Mat N) (m : ℕ) (t : ℝ) : ℝ :=
  ((m : ℝ) + 2) * ∑ a ∈ Finset.range (m + 1),
    Matrix.trace (V * Bt B V t ^ a * V * Bt B V t ^ (m - a))

/-- Third derivative. -/
def g3 (B V : Mat N) (m : ℕ) (t : ℝ) : ℝ :=
  ((m : ℝ) + 2) * ∑ a ∈ Finset.range (m + 1),
    (Matrix.trace (V * Dm (Bt B V t) V a * V * Bt B V t ^ (m - a)) +
      Matrix.trace (V * Bt B V t ^ a * V * Dm (Bt B V t) V (m - a)))

theorem hasDerivAt_g (B V : Mat N) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s => Matrix.trace (Bt B V s ^ (m + 2))) (g1 B V m t) t := by
  have h := hasDerivAt_trace (hasDerivAt_Bt_pow B V (m + 2) t)
  have e : Matrix.trace (Dm (Bt B V t) V (m + 2)) = g1 B V m t := by
    rw [show m + 2 = (m + 1) + 1 from rfl, trace_Dm, g1]
    push_cast
    ring
  rwa [e] at h

theorem hasDerivAt_g1 (B V : Mat N) (m : ℕ) (t : ℝ) :
    HasDerivAt (g1 B V m) (g2 B V m t) t := by
  have h := (hasDerivAt_trace ((hasDerivAt_Bt_pow B V (m + 1) t).const_mul V)).const_mul
    ((m : ℝ) + 2)
  have e : Matrix.trace (V * Dm (Bt B V t) V (m + 1)) =
      ∑ a ∈ Finset.range (m + 1), Matrix.trace (V * Bt B V t ^ a * V * Bt B V t ^ (m - a)) := by
    unfold Dm
    rw [Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show m + 1 - 1 - a = m - a by omega]
    simp only [mul_assoc]
  rw [e] at h
  exact h

theorem hasDerivAt_g2 (B V : Mat N) (m : ℕ) (t : ℝ) :
    HasDerivAt (g2 B V m) (g3 B V m t) t := by
  have h : ∀ a ∈ Finset.range (m + 1),
      HasDerivAt (fun s => Matrix.trace (V * Bt B V s ^ a * V * Bt B V s ^ (m - a)))
        (Matrix.trace (V * Dm (Bt B V t) V a * V * Bt B V t ^ (m - a)) +
          Matrix.trace (V * Bt B V t ^ a * V * Dm (Bt B V t) V (m - a))) t := by
    intro a _
    have h1 := hasDerivAt_trace
      ((((hasDerivAt_Bt_pow B V a t).const_mul V).mul_const V).mul
        (hasDerivAt_Bt_pow B V (m - a) t))
    rwa [Matrix.trace_add] at h1
  exact (HasDerivAt.fun_sum h).const_mul ((m : ℝ) + 2)

/-! ## Eigenvalue bounds -/
theorem abs_pow_le_pow_add_one (x : ℝ) {n k : ℕ} (hn : Even n) (hk : k ≤ n) :
    |x| ^ k ≤ x ^ n + 1 := by
  have hx : x ^ n = |x| ^ n := (hn.pow_abs x).symm
  rcases le_total |x| 1 with h | h
  · have h1 : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) h
    have h2 : 0 ≤ |x| ^ n := pow_nonneg (abs_nonneg x) n
    linarith
  · have h1 : |x| ^ k ≤ |x| ^ n := pow_le_pow_right₀ h hk
    linarith

theorem sum_abs_pow_le (C : Mat N) (hC : C.IsHermitian) {n k : ℕ} (hn : Even n) (hk : k ≤ n) :
    ∑ i, |hC.eigenvalues i| ^ k ≤ Matrix.trace (C ^ n) + N := by
  rw [StrongConv.T38.trace_pow_eq_sum C hC n]
  calc ∑ i, |hC.eigenvalues i| ^ k ≤ ∑ i, (hC.eigenvalues i ^ n + 1) :=
        Finset.sum_le_sum fun i _ => abs_pow_le_pow_add_one _ hn hk
    _ = ∑ i, hC.eigenvalues i ^ n + N := by simp [Finset.sum_add_distrib]

theorem trace_pow_add_nonneg (C : Mat N) (hC : C.IsHermitian) {n : ℕ} (hn : Even n) :
    0 ≤ Matrix.trace (C ^ n) + N :=
  le_trans (Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) 0)
    (sum_abs_pow_le C hC hn (Nat.zero_le n))

theorem abs_trace_left (C V : Mat N) (hC : C.IsHermitian) {m a : ℕ} (ha : a ≤ m) :
    |Matrix.trace (V * Dm C V a * V * C ^ (m - a))| ≤
      (a : ℝ) * (‖V‖ ^ 3 * ∑ i, |hC.eigenvalues i| ^ (m - 1)) := by
  unfold Dm
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ c ∈ Finset.range a,
      |Matrix.trace (V * (C ^ c * V * C ^ (a - 1 - c)) * V * C ^ (m - a))| ≤
        ‖V‖ ^ 3 * ∑ i, |hC.eigenvalues i| ^ (m - 1) := by
    intro c hc
    have hc' : c < a := Finset.mem_range.mp hc
    have h := StrongConv.T38.abs_trace_three_le C V V V hC c (a - 1 - c) (m - a)
    rw [show c + (a - 1 - c) + (m - a) = m - 1 by omega] at h
    have e : V * (C ^ c * V * C ^ (a - 1 - c)) * V * C ^ (m - a) =
        V * C ^ c * V * C ^ (a - 1 - c) * V * C ^ (m - a) := by simp only [mul_assoc]
    rw [e]
    calc _ ≤ _ := h
      _ = _ := by ring
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by simp only [Finset.mul_sum])

theorem abs_trace_right (C V : Mat N) (hC : C.IsHermitian) {m a : ℕ} (ha : a ≤ m) :
    |Matrix.trace (V * C ^ a * V * Dm C V (m - a))| ≤
      ((m - a : ℕ) : ℝ) * (‖V‖ ^ 3 * ∑ i, |hC.eigenvalues i| ^ (m - 1)) := by
  unfold Dm
  simp only [Finset.mul_sum, Matrix.trace_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ c ∈ Finset.range (m - a),
      |Matrix.trace (V * C ^ a * V * (C ^ c * V * C ^ (m - a - 1 - c)))| ≤
        ‖V‖ ^ 3 * ∑ i, |hC.eigenvalues i| ^ (m - 1) := by
    intro c hc
    have hc' : c < m - a := Finset.mem_range.mp hc
    have h := StrongConv.T38.abs_trace_three_le C V V V hC a c (m - a - 1 - c)
    rw [show a + c + (m - a - 1 - c) = m - 1 by omega] at h
    have e : V * C ^ a * V * (C ^ c * V * C ^ (m - a - 1 - c)) =
        V * C ^ a * V * C ^ c * V * C ^ (m - a - 1 - c) := by simp only [mul_assoc]
    rw [e]
    calc _ ≤ _ := h
      _ = _ := by ring
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by simp only [Finset.mul_sum])

theorem Bt_isHermitian {B V : Mat N} (hB : B.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    (Bt B V t).IsHermitian :=
  hB.add (hV.smul (IsSelfAdjoint.all t))

theorem abs_g1_le (B V : Mat N) (hB : B.IsHermitian) (hV : V.IsHermitian) (m : ℕ)
    (hm : Even (m + 2)) (t : ℝ) :
    |g1 B V m t| ≤ ((m : ℝ) + 2) * ‖V‖ * (Matrix.trace (Bt B V t ^ (m + 2)) + N) := by
  have hC := Bt_isHermitian hB hV t
  have h1 := StrongConv.T38.abs_trace_mul_pow_le (Bt B V t) V hC (m + 1)
  have h2 := sum_abs_pow_le (Bt B V t) hC hm (show m + 1 ≤ m + 2 by omega)
  have h3 : ‖V‖ * ∑ i, |hC.eigenvalues i| ^ (m + 1) ≤
      ‖V‖ * (Matrix.trace (Bt B V t ^ (m + 2)) + N) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg V)
  rw [g1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 2), mul_assoc]
  exact mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)

theorem abs_g3_le (B V : Mat N) (hB : B.IsHermitian) (hV : V.IsHermitian) (m : ℕ)
    (hm : Even (m + 2)) (t : ℝ) :
    |g3 B V m t| ≤ (((m : ℝ) + 2) * ‖V‖) ^ 3 * (Matrix.trace (Bt B V t ^ (m + 2)) + N) := by
  have hC := Bt_isHermitian hB hV t
  set S := ∑ i, |hC.eigenvalues i| ^ (m - 1) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) _
  have h2 : S ≤ Matrix.trace (Bt B V t ^ (m + 2)) + N :=
    sum_abs_pow_le (Bt B V t) hC hm (show m - 1 ≤ m + 2 by omega)
  have hsum : |∑ a ∈ Finset.range (m + 1),
      (Matrix.trace (V * Dm (Bt B V t) V a * V * Bt B V t ^ (m - a)) +
        Matrix.trace (V * Bt B V t ^ a * V * Dm (Bt B V t) V (m - a)))| ≤
      ((m : ℝ) + 1) * ((m : ℝ) * (‖V‖ ^ 3 * S)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ a ∈ Finset.range (m + 1),
        |Matrix.trace (V * Dm (Bt B V t) V a * V * Bt B V t ^ (m - a)) +
          Matrix.trace (V * Bt B V t ^ a * V * Dm (Bt B V t) V (m - a))| ≤
        (m : ℝ) * (‖V‖ ^ 3 * S) := by
      intro a ha
      have ha' : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have e : (m : ℝ) = (a : ℝ) + ((m - a : ℕ) : ℝ) := by
        rw [Nat.cast_sub ha']; ring
      rw [e, add_mul]
      exact (abs_add_le _ _).trans
        (add_le_add (abs_trace_left _ V hC ha') (abs_trace_right _ V hC ha'))
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have hV0 := norm_nonneg V
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [g3, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 2)]
  calc ((m : ℝ) + 2) * |_| ≤ ((m : ℝ) + 2) * (((m : ℝ) + 1) * ((m : ℝ) * (‖V‖ ^ 3 * S))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((m : ℝ) + 2) * (((m : ℝ) + 2) * (((m : ℝ) + 2) * (‖V‖ ^ 3 * S))) := by
        have hX : 0 ≤ ‖V‖ ^ 3 * S := by positivity
        gcongr <;> linarith
    _ = (((m : ℝ) + 2) * ‖V‖) ^ 3 * S := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ## Gronwall -/
theorem gronwall_core (B V : Mat N) (hB : B.IsHermitian) (hV : V.IsHermitian) (m : ℕ)
    (hm : Even (m + 2)) (t : ℝ) (ht : 0 ≤ t) :
    Matrix.trace (Bt B V t ^ (m + 2)) + N ≤
      Real.exp (((m : ℝ) + 2) * ‖V‖ * t) * (Matrix.trace (Bt B V 0 ^ (m + 2)) + N) := by
  set c := ((m : ℝ) + 2) * ‖V‖ with hc
  set φ : ℝ → ℝ := fun s => Real.exp (-(c * s)) * (Matrix.trace (Bt B V s ^ (m + 2)) + N) with hφ
  have hd : ∀ s, HasDerivAt φ (Real.exp (-(c * s)) * (-(c * 1)) *
      (Matrix.trace (Bt B V s ^ (m + 2)) + N) + Real.exp (-(c * s)) * g1 B V m s) s := by
    intro s
    exact ((((hasDerivAt_id s).const_mul c).neg).exp).mul ((hasDerivAt_g B V m s).add_const _)
  have hanti : Antitone φ := by
    refine antitone_of_deriv_nonpos (fun s => (hd s).differentiableAt) fun s => ?_
    rw [(hd s).deriv]
    have h1 := (abs_le.mp (abs_g1_le B V hB hV m hm s)).2
    have he := Real.exp_pos (-(c * s))
    have : Real.exp (-(c * s)) * (-(c * 1)) * (Matrix.trace (Bt B V s ^ (m + 2)) + N) +
        Real.exp (-(c * s)) * g1 B V m s =
        Real.exp (-(c * s)) * (g1 B V m s - c * (Matrix.trace (Bt B V s ^ (m + 2)) + N)) := by
      ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos he.le (by linarith)
  have h := hanti ht
  simp only [hφ, mul_zero, neg_zero, Real.exp_zero, one_mul] at h
  have he := Real.exp_pos (c * t)
  calc Matrix.trace (Bt B V t ^ (m + 2)) + N
      = Real.exp (c * t) * (Real.exp (-(c * t)) * (Matrix.trace (Bt B V t ^ (m + 2)) + N)) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h he.le

/-! ## Taylor -/
theorem taylor_step (f f' : ℝ → ℝ) (C : ℝ) (k : ℕ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |f' t| ≤ C * t ^ k) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, |f t| ≤ C * t ^ (k + 1) / ((k : ℝ) + 1) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => C * s ^ (k + 1) / ((k : ℝ) + 1)) (C * t ^ k) t := by
    intro t
    have h := ((hasDerivAt_pow (k + 1) t).const_mul C).div_const ((k : ℝ) + 1)
    have e : C * ((k + 1 : ℕ) * t ^ (k + 1 - 1)) / ((k : ℝ) + 1) = C * t ^ k := by
      rw [div_eq_iff hk, Nat.add_sub_cancel]
      push_cast
      ring
    rw [e] at h
    exact h
  have hmono : ∀ (u u' : ℝ → ℝ), (∀ t, HasDerivAt u (u' t) t) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ u' t) → ∀ t ∈ Set.Icc (0 : ℝ) 1, u 0 ≤ u t := by
    intro u u' hu hu' t ht
    have hm : MonotoneOn u (Set.Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
        (fun s _ => (hu s).continuousAt.continuousWithinAt)
        (fun s _ => (hu s).differentiableAt.differentiableWithinAt) fun s hs => ?_
      rw [(hu s).deriv]
      exact hu' s (interior_subset hs)
    exact hm (Set.left_mem_Icc.mpr zero_le_one) ht ht.1
  intro t ht
  have h1 := hmono _ _ (fun s => (hp s).sub (hf s))
    (fun s hs => by have := (abs_le.mp (hb s hs)).2; linarith) t ht
  have h2 := hmono _ _ (fun s => (hp s).add (hf s))
    (fun s hs => by have := (abs_le.mp (hb s hs)).1; linarith) t ht
  have z : C * (0 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) = 0 := by simp
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2
  rw [h0, z] at h1 h2
  rw [abs_le]
  constructor <;> linarith

theorem taylor_core (B V : Mat N) (m : ℕ) (K : ℝ)
    (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g3 B V m t| ≤ K) :
    |Matrix.trace (Bt B V 1 ^ (m + 2)) - Matrix.trace (Bt B V 0 ^ (m + 2)) - g1 B V m 0 -
      g2 B V m 0 / 2| ≤ K / 6 := by
  have s3 := taylor_step (fun t => g2 B V m t - g2 B V m 0) (g3 B V m) K 0
    (fun t => (hasDerivAt_g2 B V m t).sub_const _) (by simp) (by simpa using hK)
  have s2 := taylor_step (fun t => g1 B V m t - g1 B V m 0 - g2 B V m 0 * t)
    (fun t => g2 B V m t - g2 B V m 0) K 1
    (fun t => ((hasDerivAt_g1 B V m t).sub_const _).sub
      (by simpa using (hasDerivAt_id t).const_mul (g2 B V m 0)))
    (by simp) (fun t ht => by simpa using s3 t ht)
  have s1 := taylor_step
    (fun t => Matrix.trace (Bt B V t ^ (m + 2)) - Matrix.trace (Bt B V 0 ^ (m + 2)) -
      g1 B V m 0 * t - g2 B V m 0 * t ^ 2 / 2)
    (fun t => g1 B V m t - g1 B V m 0 - g2 B V m 0 * t) (K / 2) 2
    (fun t => by
      have h : HasDerivAt (fun t => Matrix.trace (Bt B V t ^ (m + 2)) -
          Matrix.trace (Bt B V 0 ^ (m + 2)) - g1 B V m 0 * t - g2 B V m 0 * t ^ 2 / 2)
          (g1 B V m t - g1 B V m 0 * 1 - g2 B V m 0 * (((2 : ℕ) : ℝ) * t ^ 1) / 2) t :=
        (((hasDerivAt_g B V m t).sub_const (Matrix.trace (Bt B V 0 ^ (m + 2)))).sub
        ((hasDerivAt_id t).const_mul (g1 B V m 0))).sub
        (((hasDerivAt_pow 2 t).const_mul (g2 B V m 0)).div_const 2)
      have e : g1 B V m t - g1 B V m 0 * 1 - g2 B V m 0 * (((2 : ℕ) : ℝ) * t ^ 1) / 2 =
          g1 B V m t - g1 B V m 0 - g2 B V m 0 * t := by
        push_cast
        ring
      rw [e] at h
      exact h)
    (by simp) (fun t ht => by
      have := s2 t ht
      norm_num at this ⊢
      linarith)
  have := s1 1 (Set.right_mem_Icc.mpr zero_le_one)
  norm_num at this ⊢
  linarith

/-! ## The two stubs -/
theorem Bt_eq (θ : ℝ) (n : ℕ) (M W : Mat N) (t : ℝ) :
    1 + (θ / (n : ℝ)) • (M + t • W) =
      Bt (1 + (θ / (n : ℝ)) • M) ((θ / (n : ℝ)) • W) t := by
  simp only [Bt, smul_add, add_assoc, smul_comm t]

theorem Ft_add_le {N : ℕ} (θ : ℝ) (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (M W : Mat N)
    (hM : M.IsHermitian) (hW : W.IsHermitian) :
    Ft θ n (M + W) ≤ Real.exp (|θ| * ‖W‖) * Ft θ n M := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set r : ℝ := θ / ((m + 2 : ℕ) : ℝ) with hr
  have hB : (1 + r • M).IsHermitian :=
    Matrix.isHermitian_one.add (hM.smul (IsSelfAdjoint.all r))
  have hV : (r • W).IsHermitian := hW.smul (IsSelfAdjoint.all r)
  have h := gronwall_core (1 + r • M) (r • W) hB hV m hn 1 zero_le_one
  have e1 : Ft θ (m + 2) (M + W) = Matrix.trace (Bt (1 + r • M) (r • W) 1 ^ (m + 2)) + N := by
    rw [Ft, Fn, ← Bt_eq, one_smul]
  have e0 : Ft θ (m + 2) M = Matrix.trace (Bt (1 + r • M) (r • W) 0 ^ (m + 2)) + N := by
    rw [Ft, Fn, ← Bt_eq, zero_smul, add_zero]
  have ec : ((m : ℝ) + 2) * ‖r • W‖ * 1 = |θ| * ‖W‖ := by
    rw [norm_smul, Real.norm_eq_abs, hr, abs_div]
    push_cast
    rw [abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 2)]
    field_simp
  rw [e1, e0, ← ec]
  exact h

end StrongConv.T38.PartB
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part B: second-order Taylor expansion of the test function -/
alias Ft_add_le := StrongConv.T38.PartB.Ft_add_le

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartB
open StrongConv.T38
variable {N : ℕ}
theorem abs_Fn_add_sub_le {N : ℕ} (θ : ℝ) (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (M W : Mat N)
    (hM : M.IsHermitian) (hW : W.IsHermitian) :
    |Fn θ n (M + W) - Fn θ n M - linTerm θ n M W - quadTerm θ n M W| ≤
      |θ| ^ 3 * ‖W‖ ^ 3 / 6 * Real.exp (|θ| * ‖W‖) * Ft θ n M := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set r : ℝ := θ / ((m + 2 : ℕ) : ℝ) with hr
  have hm2 : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hm0 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hrm : ((m : ℝ) + 2) * r = θ := by rw [hr, hm2]; field_simp
  have hB : (1 + r • M).IsHermitian :=
    Matrix.isHermitian_one.add (hM.smul (IsSelfAdjoint.all r))
  have hV : (r • W).IsHermitian := hW.smul (IsSelfAdjoint.all r)
  set B := 1 + r • M with hBdef
  set V := r • W with hVdef
  have hB0 : Bt B V 0 = B := by simp [Bt]
  have e1 : Fn θ (m + 2) (M + W) = Matrix.trace (Bt B V 1 ^ (m + 2)) := by
    rw [Fn, ← Bt_eq, one_smul]
  have e0 : Fn θ (m + 2) M = Matrix.trace (Bt B V 0 ^ (m + 2)) := by
    rw [Fn, ← Bt_eq, zero_smul, add_zero]
  have ec : ((m : ℝ) + 2) * ‖V‖ = |θ| * ‖W‖ := by
    have h1 : |θ| = ((m : ℝ) + 2) * |r| := by rw [← hrm, abs_mul, abs_of_pos hm0]
    rw [hVdef, norm_smul, Real.norm_eq_abs, ← mul_assoc, h1]
  have el : linTerm θ (m + 2) M W = g1 B V m 0 := by
    rw [linTerm, g1, hB0, hVdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
      hrm]
    rfl
  have eq : quadTerm θ (m + 2) M W = g2 B V m 0 / 2 := by
    rw [quadTerm, g2, hB0, show m + 2 - 1 = m + 1 from rfl]
    have : ∀ a ∈ Finset.range (m + 1),
        Matrix.trace (V * B ^ a * V * B ^ (m - a)) =
          r ^ 2 * Matrix.trace (W * (1 + (θ / ((m + 2 : ℕ) : ℝ)) • M) ^ a * W *
            (1 + (θ / ((m + 2 : ℕ) : ℝ)) • M) ^ (m + 2 - 2 - a)) := by
      intro a _
      rw [hVdef]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [show m + 2 - 2 - a = m - a from rfl]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hm2]
    have hθ : θ = ((m : ℝ) + 2) * r := hrm.symm
    rw [hθ]
    field_simp
  set c := |θ| * ‖W‖ with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hF0 : 0 ≤ Ft θ (m + 2) M := by
    rw [Ft, e0]; exact trace_pow_add_nonneg _ (Bt_isHermitian hB hV 0) hn
  have hK : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |g3 B V m t| ≤ c ^ 3 * (Real.exp c * Ft θ (m + 2) M) := by
    intro t ht
    have h3 := abs_g3_le B V hB hV m hn t
    have hg := gronwall_core B V hB hV m hn t ht.1
    rw [ec] at h3 hg
    rw [← e0] at hg
    have hexp : Real.exp (c * t) ≤ Real.exp c := by
      apply Real.exp_le_exp.mpr
      nlinarith [ht.2]
    have h4 : Matrix.trace (Bt B V t ^ (m + 2)) + N ≤ Real.exp c * Ft θ (m + 2) M :=
      hg.trans (by rw [Ft]; exact mul_le_mul_of_nonneg_right hexp (by rw [Ft] at hF0; exact hF0))
    exact h3.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
  have h := taylor_core B V m _ hK
  rw [e1, e0, el, eq]
  calc _ ≤ _ := h
    _ = _ := by rw [hcdef]; ring

end StrongConv.T38.PartB
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias abs_Fn_add_sub_le := StrongConv.T38.PartB.abs_Fn_add_sub_le

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartC
/-!
# T38 Part C: the permutation summand

`xMat τ` is symmetric, has norm at most `4`, mean zero over `τ`, and the entry covariance
`2 (P_ac P_be + P_ae P_bc) / (N − 1)`.
-/
/-! ### Counting over permutations (real-valued copies of the lemmas of the published reduction) -/
lemma sum_perm_apply_indep {N : ℕ} (g : Fin N → ℝ) (b b' : Fin N) :
    ∑ τ : Equiv.Perm (Fin N), g (τ b) = ∑ τ : Equiv.Perm (Fin N), g (τ b') := by
  refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap b b')) _ _ fun τ => ?_
  simp [Equiv.Perm.mul_apply]

lemma card_perm_R (N : ℕ) : ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ℝ) = (N.factorial : ℝ) := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- One-point sums. -/
lemma sum_perm_one {N : ℕ} (g : Fin N → ℝ) (b : Fin N) :
    (N : ℝ) * ∑ τ : Equiv.Perm (Fin N), g (τ b) = N.factorial * ∑ a, g a := by
  have h1 : (N : ℝ) * ∑ τ : Equiv.Perm (Fin N), g (τ b) =
      ∑ b' : Fin N, ∑ τ : Equiv.Perm (Fin N), g (τ b') := by
    rw [Finset.sum_congr rfl fun b' _ => (sum_perm_apply_indep g b b').symm]
    simp
  rw [h1, Finset.sum_comm]
  have : ∀ τ : Equiv.Perm (Fin N), ∑ b', g (τ b') = ∑ a, g a := fun τ =>
    Equiv.sum_comp τ g
  rw [Finset.sum_congr rfl fun τ _ => this τ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_perm_R]

lemma sum_perm_two_indep {N : ℕ} (g : Fin N → Fin N → ℝ) (b b' b'' : Fin N) (h' : b' ≠ b)
    (h'' : b'' ≠ b) :
    ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b') = ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b'') := by
  refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap b' b'')) _ _ fun τ => ?_
  simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h'.symm h''.symm]

/-- Two-point sums. -/
lemma sum_perm_two {N : ℕ} (g : Fin N → Fin N → ℝ) (b b' : Fin N) (hb : b' ≠ b) :
    ((N : ℝ) * (N - 1)) * ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b') =
      N.factorial * ∑ a, ∑ a' ∈ Finset.univ.erase a, g a a' := by
  have hcard : ((Finset.univ.erase b).card : ℝ) = (N : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ N := by have := b.isLt; omega
    push_cast [Nat.cast_sub this]; ring
  have h1 : ((N : ℝ) - 1) * ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b') =
      ∑ b'' ∈ Finset.univ.erase b, ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b'') := by
    rw [Finset.sum_congr rfl fun b'' hb'' =>
      (sum_perm_two_indep g b b' b'' hb (Finset.ne_of_mem_erase hb'')).symm]
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have h2 : ∀ τ : Equiv.Perm (Fin N), ∑ b'' ∈ Finset.univ.erase b, g (τ b) (τ b'') =
      ∑ a' ∈ Finset.univ.erase (τ b), g (τ b) a' := by
    intro τ
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_erase_eq_sub (Finset.mem_univ _),
      Equiv.sum_comp τ (g (τ b))]
  calc ((N : ℝ) * (N - 1)) * ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b')
      = (N : ℝ) * (((N : ℝ) - 1) * ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b')) := by ring
    _ = (N : ℝ) * ∑ τ : Equiv.Perm (Fin N), ∑ a' ∈ Finset.univ.erase (τ b), g (τ b) a' := by
        rw [h1, Finset.sum_comm, Finset.sum_congr rfl fun τ _ => h2 τ]
    _ = N.factorial * ∑ a, ∑ a' ∈ Finset.univ.erase a, g a a' :=
        sum_perm_one (fun a => ∑ a' ∈ Finset.univ.erase a, g a a') b

/-! ### The centred permutation matrix `T = Π − J/N` -/
/-- `T_τ a b = [τ b = a] − 1/N`. -/
def tEnt {N : ℕ} (τ : Equiv.Perm (Fin N)) (a b : Fin N) : ℝ :=
  (if τ b = a then (1 : ℝ) else 0) - 1 / (N : ℝ)

lemma xMat_apply {N : ℕ} (τ : Equiv.Perm (Fin N)) (a b : Fin N) :
    xMat τ a b = tEnt τ a b + tEnt τ b a := by
  simp only [xMat, tEnt, Matrix.of_apply]; ring

/-- `P(τ b = a) = 1/N`. -/
lemma avg_ind {N : ℕ} (a b : Fin N) :
    (∑ τ : Equiv.Perm (Fin N), (if τ b = a then (1 : ℝ) else 0)) / (N.factorial : ℝ) =
      1 / (N : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := by
    have := b.isLt; exact_mod_cast (show N ≠ 0 by omega)
  have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have h := sum_perm_one (fun c => if c = a then (1 : ℝ) else 0) b
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one] at h
  rw [div_eq_div_iff hF hN, one_mul, mul_comm, h]

/-- `P(τ b = a ∧ τ e = c)`, for `b = e`. -/
lemma avg_ind_same {N : ℕ} (a b c : Fin N) :
    (∑ τ : Equiv.Perm (Fin N), (if τ b = a then (1 : ℝ) else 0) * (if τ b = c then 1 else 0)) /
      (N.factorial : ℝ) = (if a = c then 1 else 0) / (N : ℝ) := by
  by_cases hac : a = c
  · subst hac
    simp only [if_true, ← avg_ind a b]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp
  · rw [if_neg hac, zero_div]
    have : ∀ τ : Equiv.Perm (Fin N),
        (if τ b = a then (1 : ℝ) else 0) * (if τ b = c then 1 else 0) = 0 := by
      intro τ
      by_cases h1 : τ b = a
      · have : τ b ≠ c := fun h => hac (h1.symm.trans h)
        simp [this]
      · simp [h1]
    simp [this]

/-- `P(τ b = a ∧ τ e = c)`, for `b ≠ e`. -/
lemma avg_ind_ne {N : ℕ} (a b c e : Fin N) (hbe : b ≠ e) :
    (∑ τ : Equiv.Perm (Fin N), (if τ b = a then (1 : ℝ) else 0) * (if τ e = c then 1 else 0)) /
      (N.factorial : ℝ) = (if a = c then 0 else 1) / ((N : ℝ) * (N - 1)) := by
  have hN2 : 2 ≤ N := by
    have h1 := b.isLt; have h2 := e.isLt
    have : (b : ℕ) ≠ e := fun h => hbe (Fin.ext h)
    omega
  have hN : (N : ℝ) ≠ 0 := by positivity
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have h := sum_perm_two (fun u v => (if u = a then (1 : ℝ) else 0) * (if v = c then 1 else 0))
    b e hbe.symm
  have h3 : ∀ u : Fin N, ∑ v ∈ Finset.univ.erase u,
      (if u = a then (1 : ℝ) else 0) * (if v = c then 1 else 0) =
      if u = a then (if a = c then 0 else 1) else 0 := by
    intro u
    by_cases hu : u = a
    · subst hu
      simp only [if_true, one_mul, Finset.sum_ite_eq', Finset.mem_erase, Finset.mem_univ,
        and_true]
      by_cases huc : u = c
      · simp [huc]
      · simp [huc, Ne.symm huc]
    · simp [hu]
  rw [Finset.sum_congr rfl fun u _ => h3 u, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h
  rw [div_eq_div_iff hF (mul_ne_zero hN hN1), mul_comm, h]
  ring

/-- `E T_ab = 0`. -/
lemma avg_tEnt {N : ℕ} (a b : Fin N) :
    (∑ τ : Equiv.Perm (Fin N), tEnt τ a b) / (N.factorial : ℝ) = 0 := by
  have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  simp only [tEnt, Finset.sum_sub_distrib, sub_div, avg_ind, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_perm_R]
  field_simp
  simp

/-- `E[T_ab T_ce] = P_ac P_be / (N − 1)`. -/
lemma avg_tEnt_mul {N : ℕ} (hN2 : 2 ≤ N) (a b c e : Fin N) :
    (∑ τ : Equiv.Perm (Fin N), tEnt τ a b * tEnt τ c e) / (N.factorial : ℝ) =
      pMat N a c * pMat N b e / ((N : ℝ) - 1) := by
  have hN : (N : ℝ) ≠ 0 := by positivity
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have hP : ∀ x y : Fin N, pMat N x y = (if x = y then (1 : ℝ) else 0) - 1 / (N : ℝ) := by
    intro x y
    simp [pMat, Matrix.one_apply]
  have hexp : ∀ τ : Equiv.Perm (Fin N), tEnt τ a b * tEnt τ c e =
      (if τ b = a then (1 : ℝ) else 0) * (if τ e = c then 1 else 0)
        - 1 / (N : ℝ) * (if τ b = a then (1 : ℝ) else 0)
        - 1 / (N : ℝ) * (if τ e = c then (1 : ℝ) else 0) + 1 / (N : ℝ) ^ 2 := by
    intro τ; simp only [tEnt]; ring
  have hmain : (∑ τ : Equiv.Perm (Fin N), tEnt τ a b * tEnt τ c e) / (N.factorial : ℝ) =
      (∑ τ : Equiv.Perm (Fin N), (if τ b = a then (1 : ℝ) else 0) * (if τ e = c then 1 else 0)) /
        (N.factorial : ℝ) - 1 / (N : ℝ) ^ 2 := by
    rw [Finset.sum_congr rfl fun τ _ => hexp τ]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, add_div, sub_div,
      mul_div_assoc, avg_ind, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_perm_R]
    field_simp
    ring
  rw [hmain, hP, hP]
  by_cases hbe : b = e
  · subst hbe
    rw [avg_ind_same]
    by_cases hac : a = c
    · simp only [hac, if_true]; field_simp
    · simp only [hac, if_false, if_true]; field_simp
  · rw [avg_ind_ne a b c e hbe]
    by_cases hac : a = c
    · simp only [hac, hbe, if_true, if_false]; field_simp; ring
    · simp only [hac, hbe, if_false]; field_simp; ring

/-! ### Norm -/
/-- The permutation matrix `Π_τ`. -/
def piMat {N : ℕ} (τ : Equiv.Perm (Fin N)) : Mat N :=
  Matrix.of fun a b => if τ b = a then (1 : ℝ) else 0

/-- `J/N`. -/
def qMat (N : ℕ) : Mat N := Matrix.of fun _ _ => 1 / (N : ℝ)

lemma norm_le_one_of_star_mul_self {N : ℕ} (A B : Mat N) (h : star A * A = B) (hB : ‖B‖ ≤ 1) :
    ‖A‖ ≤ 1 := by
  have h1 : ‖A‖ * ‖A‖ = ‖B‖ := by rw [← h, CStarRing.norm_star_mul_self]
  nlinarith [norm_nonneg A]

lemma norm_le_one_of_proj {N : ℕ} (E : Mat N) (h : star E * E = E) : ‖E‖ ≤ 1 := by
  have h1 : ‖E‖ * ‖E‖ = ‖E‖ := by
    conv_rhs => rw [← h]
    rw [CStarRing.norm_star_mul_self]
  by_contra hc
  rw [not_le] at hc
  nlinarith [norm_nonneg E]

lemma norm_one_le {N : ℕ} : ‖(1 : Mat N)‖ ≤ 1 :=
  norm_le_one_of_proj 1 (by simp)

lemma norm_piMat_le {N : ℕ} (τ : Equiv.Perm (Fin N)) : ‖piMat τ‖ ≤ 1 := by
  refine norm_le_one_of_star_mul_self (piMat τ) 1 ?_ norm_one_le
  ext a b
  simp [piMat, Matrix.mul_apply, Matrix.one_apply, Matrix.star_eq_conjTranspose]

lemma norm_qMat_le (N : ℕ) : ‖qMat N‖ ≤ 1 := by
  refine norm_le_one_of_proj _ ?_
  ext a b
  have hN : (N : ℝ) ≠ 0 := by
    have := b.isLt; exact_mod_cast (show N ≠ 0 by omega)
  simp only [qMat, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.of_apply, star_trivial, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

lemma xMat_eq {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    xMat τ = piMat τ + star (piMat τ) - (2 : ℝ) • qMat N := by
  ext a b
  simp [xMat, piMat, qMat, Matrix.star_eq_conjTranspose]
  ring

/-! ### The four stubs -/
theorem xMat_isHermitian {N : ℕ} (τ : Equiv.Perm (Fin N)) : (xMat τ).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, star_trivial, xMat_apply]
  ring

end StrongConv.T38.PartC
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part C: the permutation summand -/
alias xMat_isHermitian := StrongConv.T38.PartC.xMat_isHermitian

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartC
theorem norm_xMat_le {N : ℕ} (τ : Equiv.Perm (Fin N)) : ‖xMat τ‖ ≤ 4 := by
  rw [xMat_eq]
  have h1 := norm_piMat_le τ
  have h2 : ‖star (piMat τ)‖ ≤ 1 := by rw [norm_star]; exact h1
  have h3 : ‖(2 : ℝ) • qMat N‖ ≤ 2 := by
    rw [norm_smul]
    have := norm_qMat_le N
    simp only [Real.norm_ofNat]
    linarith
  calc ‖piMat τ + star (piMat τ) - (2 : ℝ) • qMat N‖
      ≤ ‖piMat τ + star (piMat τ)‖ + ‖(2 : ℝ) • qMat N‖ := norm_sub_le _ _
    _ ≤ ‖piMat τ‖ + ‖star (piMat τ)‖ + ‖(2 : ℝ) • qMat N‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ 4 := by linarith

end StrongConv.T38.PartC
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias norm_xMat_le := StrongConv.T38.PartC.norm_xMat_le

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartC
theorem sum_xMat {N : ℕ} (hN : 1 ≤ N) (a b : Fin N) :
    ∑ τ : Equiv.Perm (Fin N), xMat τ a b = 0 := by
  have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have h1 := avg_tEnt a b
  have h2 := avg_tEnt b a
  rw [div_eq_zero_iff, or_iff_left hF] at h1 h2
  simp only [xMat_apply, Finset.sum_add_distrib, h1, h2, add_zero]

end StrongConv.T38.PartC
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias sum_xMat := StrongConv.T38.PartC.sum_xMat

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartC
theorem sum_xMat_mul {N : ℕ} (hN : 2 ≤ N) (a b c e : Fin N) :
    (∑ τ : Equiv.Perm (Fin N), xMat τ a b * xMat τ c e) / (N.factorial : ℝ) =
      2 * (pMat N a c * pMat N b e + pMat N a e * pMat N b c) / ((N : ℝ) - 1) := by
  have hexp : ∀ τ : Equiv.Perm (Fin N), xMat τ a b * xMat τ c e =
      tEnt τ a b * tEnt τ c e + tEnt τ a b * tEnt τ e c + tEnt τ b a * tEnt τ c e +
        tEnt τ b a * tEnt τ e c := by
    intro τ; simp only [xMat_apply]; ring
  rw [Finset.sum_congr rfl fun τ _ => hexp τ]
  simp only [Finset.sum_add_distrib, add_div, avg_tEnt_mul hN]
  ring

end StrongConv.T38.PartC
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias sum_xMat_mul := StrongConv.T38.PartC.sum_xMat_mul

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartD
/-!
# T38 Part D: mean and entry covariance of the Gaussian summand
-/
theorem pMat_apply (N : ℕ) (a b : Fin N) :
    pMat N a b = (if a = b then (1 : ℝ) else 0) - 1 / (N : ℝ) := by
  simp [pMat, Matrix.one_apply]

theorem pMat_symm (N : ℕ) (a b : Fin N) : pMat N a b = pMat N b a := by
  simp [pMat_apply, eq_comm]

/-- `P Pᵀ = P`, entrywise. -/
theorem sum_pMat_mul_pMat (N : ℕ) (a c : Fin N) :
    ∑ k, pMat N a k * pMat N c k = pMat N a c := by
  have hN : (N : ℝ) ≠ 0 := by
    have : 0 < N := Fin.pos a
    positivity
  simp only [pMat_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_ite, ite_mul, mul_one, mul_zero,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  field_simp
  ring

/-- The coefficient of `w p` in the entry `(a, b)` of `gMat w`. -/
def coef {N : ℕ} (a b : Fin N) (p : Fin N × Fin N) : ℝ :=
  (Real.sqrt ((N : ℝ) - 1))⁻¹ * (pMat N a p.1 * pMat N p.2 b + pMat N a p.2 * pMat N p.1 b)

theorem gMat_apply {N : ℕ} (w : Fin N × Fin N → ℝ) (a b : Fin N) :
    gMat w a b = ∑ p, coef a b p * w p := by
  simp only [gMat, coef, Matrix.smul_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply,
    smul_eq_mul, Fintype.sum_prod_type]
  have hL : ∑ l, (∑ k, pMat N a k * (w (k, l) + w (l, k))) * pMat N l b =
      (∑ k, ∑ l, pMat N a k * pMat N l b * w (k, l)) +
        ∑ k, ∑ l, pMat N a l * pMat N k b * w (k, l) := by
    rw [Finset.sum_comm (f := fun k l => pMat N a k * pMat N l b * w (k, l)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hL, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem gMat_isHermitian {N : ℕ} (w : Fin N × Fin N → ℝ) : (gMat w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [star_trivial, gMat_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [coef]
  rw [pMat_symm N b p.1, pMat_symm N p.2 a, pMat_symm N b p.2, pMat_symm N p.1 a]
  ring

end StrongConv.T38.PartD
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part D: the Gaussian summand has the same mean and covariance -/
alias gMat_isHermitian := StrongConv.T38.PartD.gMat_isHermitian

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartD
instance (N : ℕ) : IsProbabilityMeasure (gauss N) := by
  unfold gauss; infer_instance

theorem memLp_eval {N : ℕ} (p : Fin N × Fin N) :
    MemLp (fun w : Fin N × Fin N → ℝ => w p) 2 (gauss N) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin N × Fin N => gaussianReal 0 1) p)

theorem integrable_eval {N : ℕ} (p : Fin N × Fin N) :
    Integrable (fun w : Fin N × Fin N → ℝ => w p) (gauss N) :=
  (memLp_eval p).integrable (by norm_num)

theorem integrable_eval_mul {N : ℕ} (p q : Fin N × Fin N) :
    Integrable (fun w : Fin N × Fin N → ℝ => w p * w q) (gauss N) :=
  (memLp_eval p).integrable_mul (memLp_eval q)

theorem integral_eval {N : ℕ} (p : Fin N × Fin N) :
    ∫ w : Fin N × Fin N → ℝ, w p ∂gauss N = 0 := by
  have h := measurePreserving_eval (fun _ : Fin N × Fin N => gaussianReal 0 1) p
  have h2 : ∫ x, x ∂((gauss N).map (Function.eval p)) = ∫ w, w p ∂gauss N :=
    integral_map h.measurable.aemeasurable aestronglyMeasurable_id
  rw [← h2]
  unfold gauss
  rw [h.map_eq, integral_id_gaussianReal]

theorem integral_eval_sq {N : ℕ} (p : Fin N × Fin N) :
    ∫ w : Fin N × Fin N → ℝ, w p * w p ∂gauss N = 1 := by
  have h := measurePreserving_eval (fun _ : Fin N × Fin N => gaussianReal 0 1) p
  have h2 : ∫ x, x * x ∂((gauss N).map (Function.eval p)) = ∫ w, w p * w p ∂gauss N :=
    integral_map h.measurable.aemeasurable (by fun_prop)
  rw [← h2]
  unfold gauss
  rw [h.map_eq]
  have h3 := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero aemeasurable_id (by simp [integral_id_gaussianReal])] at h3
  simpa [sq] using h3

theorem integral_eval_mul {N : ℕ} (p q : Fin N × Fin N) :
    ∫ w : Fin N × Fin N → ℝ, w p * w q ∂gauss N = if p = q then 1 else 0 := by
  split_ifs with h
  · subst h
    exact integral_eval_sq p
  · have hind := iIndepFun_pi (μ := fun _ : Fin N × Fin N => gaussianReal 0 1)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
    have h2 := (hind.indepFun h).integral_mul_eq_mul_integral
      (integrable_eval p).aestronglyMeasurable (integrable_eval q).aestronglyMeasurable
    have h3 := integral_eval p
    simp only [gauss, id] at h2 h3 ⊢
    simp only [Pi.mul_apply] at h2
    rw [h2, h3, zero_mul]

theorem integrable_gMat {N : ℕ} (a b : Fin N) :
    Integrable (fun w => gMat w a b) (gauss N) := by
  simp only [gMat_apply]
  exact integrable_finsetSum _ fun p _ => (integrable_eval p).const_mul _

end StrongConv.T38.PartD
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias integrable_gMat := StrongConv.T38.PartD.integrable_gMat

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartD
theorem integrable_gMat_mul {N : ℕ} (a b c e : Fin N) :
    Integrable (fun w => gMat w a b * gMat w c e) (gauss N) := by
  simp only [gMat_apply, Finset.sum_mul_sum]
  refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => ?_
  have := (integrable_eval_mul p q).const_mul (coef a b p * coef c e q)
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  ring

end StrongConv.T38.PartD
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias integrable_gMat_mul := StrongConv.T38.PartD.integrable_gMat_mul

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartD
theorem integral_gMat {N : ℕ} (a b : Fin N) : ∫ w, gMat w a b ∂gauss N = 0 := by
  simp only [gMat_apply]
  rw [integral_finsetSum _ fun p _ => (integrable_eval p).const_mul _]
  simp [integral_const_mul, integral_eval]

end StrongConv.T38.PartD
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias integral_gMat := StrongConv.T38.PartD.integral_gMat

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartD
theorem integral_gMat_mul_eq_sum {N : ℕ} (a b c e : Fin N) :
    ∫ w, gMat w a b * gMat w c e ∂gauss N = ∑ p, coef a b p * coef c e p := by
  have hfun : ∀ w : Fin N × Fin N → ℝ, gMat w a b * gMat w c e =
      ∑ p, ∑ q, (coef a b p * coef c e q) * (w p * w q) := by
    intro w
    rw [gMat_apply, gMat_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp only [hfun]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
    (integrable_eval_mul p q).const_mul _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => (integrable_eval_mul p q).const_mul _]
  simp [integral_const_mul, integral_eval_mul]

theorem integral_gMat_mul {N : ℕ} (hN : 2 ≤ N) (a b c e : Fin N) :
    ∫ w, gMat w a b * gMat w c e ∂gauss N =
      2 * (pMat N a c * pMat N b e + pMat N a e * pMat N b c) / ((N : ℝ) - 1) := by
  rw [integral_gMat_mul_eq_sum]
  have hpos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hs : (Real.sqrt ((N : ℝ) - 1))⁻¹ * (Real.sqrt ((N : ℝ) - 1))⁻¹ = ((N : ℝ) - 1)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  have key : ∀ x y z u : Fin N, ∑ k, ∑ l, pMat N x k * pMat N l y * (pMat N z k * pMat N l u) =
      pMat N x z * pMat N y u := by
    intro x y z u
    rw [← sum_pMat_mul_pMat N x z, ← sum_pMat_mul_pMat N y u, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [pMat_symm N l y, pMat_symm N l u]
    ring
  have key2 : ∀ x y z u : Fin N, ∑ k, ∑ l, pMat N x k * pMat N l y * (pMat N z l * pMat N k u) =
      pMat N x u * pMat N y z := by
    intro x y z u
    rw [← sum_pMat_mul_pMat N x u, ← sum_pMat_mul_pMat N y z, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [pMat_symm N l y, pMat_symm N k u]
    ring
  have key3 : ∀ x y z u : Fin N, ∑ k, ∑ l, pMat N x l * pMat N k y * (pMat N z k * pMat N l u) =
      pMat N x u * pMat N y z := by
    intro x y z u
    rw [Finset.sum_comm]
    exact key2 x y z u
  have key4 : ∀ x y z u : Fin N, ∑ k, ∑ l, pMat N x l * pMat N k y * (pMat N z l * pMat N k u) =
      pMat N x z * pMat N y u := by
    intro x y z u
    rw [Finset.sum_comm]
    exact key x y z u
  have expand : ∀ p : Fin N × Fin N, coef a b p * coef c e p =
      ((N : ℝ) - 1)⁻¹ * (pMat N a p.1 * pMat N p.2 b * (pMat N c p.1 * pMat N p.2 e) +
        pMat N a p.1 * pMat N p.2 b * (pMat N c p.2 * pMat N p.1 e) +
        pMat N a p.2 * pMat N p.1 b * (pMat N c p.1 * pMat N p.2 e) +
        pMat N a p.2 * pMat N p.1 b * (pMat N c p.2 * pMat N p.1 e)) := by
    intro p
    simp only [coef, ← hs]
    ring
  simp only [expand, ← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_add_distrib,
    key, key2, key3, key4]
  field_simp
  ring

end StrongConv.T38.PartD
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias integral_gMat_mul := StrongConv.T38.PartD.integral_gMat_mul

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartE
/-!
# T38 Part E, file 2: the norm of the Gaussian model

`‖gSum w‖ ≤ (N − 1)^(-1/2) ‖H(w)‖` with `H = ∑ᵢ (Wᵢ + Wᵢᵀ)`; the quadratic forms `x ↦ ⟨x, H x⟩`
are linear forms of the flattened Gaussian vector, so file 1 applies along a dense sequence of
the unit sphere.
-/
/-! ### Matrix preliminaries -/
/-- `H(w) = ∑ᵢ (Wᵢ + Wᵢᵀ)`. -/
def hSum {d N : ℕ} (w : Fin d → Fin N × Fin N → ℝ) : Mat N :=
  ∑ i, (Matrix.of (fun a b => w i (a, b)) + Matrix.of (fun a b => w i (b, a)))

theorem pMat_mul_self {N : ℕ} (hN : 1 ≤ N) : pMat N * pMat N = pMat N := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hJ : (Matrix.of (fun _ _ => (1 : ℝ)) : Mat N) * Matrix.of (fun _ _ => (1 : ℝ)) =
      (N : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) := by
    ext a b
    simp [Matrix.mul_apply]
  unfold pMat
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, hJ, smul_smul]
  have : 1 / (N : ℝ) * (1 / (N : ℝ)) * (N : ℝ) = 1 / (N : ℝ) := by field_simp
  rw [this]
  abel

theorem pMat_conjTranspose {N : ℕ} : (pMat N)ᴴ = pMat N := by
  ext a b
  simp [pMat, Matrix.one_apply, eq_comm]

theorem norm_pMat_le {N : ℕ} (hN : 1 ≤ N) : ‖pMat N‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (pMat N)
  rw [pMat_conjTranspose, pMat_mul_self hN] at h
  by_contra hc
  rw [not_le] at hc
  nlinarith [norm_nonneg (pMat N)]

theorem gSum_eq {d N : ℕ} (w : Fin d → Fin N × Fin N → ℝ) :
    gSum w = (Real.sqrt ((N : ℝ) - 1))⁻¹ • (pMat N * hSum w * pMat N) := by
  simp only [gSum, gMat, hSum, Finset.smul_sum, Finset.mul_sum, Finset.sum_mul]

theorem norm_gSum_le {d N : ℕ} (hN : 1 ≤ N) (w : Fin d → Fin N × Fin N → ℝ) :
    ‖gSum w‖ ≤ (Real.sqrt ((N : ℝ) - 1))⁻¹ * ‖hSum w‖ := by
  rw [gSum_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hp := norm_pMat_le hN
  calc ‖pMat N * hSum w * pMat N‖ ≤ ‖pMat N * hSum w‖ * ‖pMat N‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖pMat N‖ * ‖hSum w‖) * ‖pMat N‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖hSum w‖) * 1 := by
        gcongr
    _ = ‖hSum w‖ := by ring

theorem hSum_isHermitian {d N : ℕ} (w : Fin d → Fin N × Fin N → ℝ) : (hSum w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [hSum, Matrix.sum_apply, Matrix.add_apply, Matrix.of_apply, star_trivial]
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

/-- The coefficient vector of the quadratic form `x ↦ ⟨x, H(w) x⟩` in the flattened `w`. -/
def cvec (d : ℕ) {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) : Fin d × (Fin N × Fin N) → ℝ :=
  fun j => 2 * x j.2.1 * x j.2.2

end StrongConv.T38.PartE
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartS
/-!
# T38 Part S: one Lindeberg swap
-/
/-- The common covariance of the entries of `xMat` and `gMat`. -/
def cov (N : ℕ) (a b c e : Fin N) : ℝ :=
  2 * (pMat N a c * pMat N b e + pMat N a e * pMat N b c) / ((N : ℝ) - 1)

/-- The common value of the averaged second-order term. -/
def qExpr {N : ℕ} (θ : ℝ) (n : ℕ) (M : Mat N) : ℝ :=
  θ ^ 2 / (2 * (n : ℝ)) * ∑ k ∈ Finset.range (n - 1), ∑ a, ∑ e, ∑ c, ∑ b,
    cov N a b c e * (((1 + (θ / (n : ℝ)) • M) ^ k) b c * ((1 + (θ / (n : ℝ)) • M) ^ (n - 2 - k)) e a)

/-- The constant of the swap. -/
def K3 : ℝ := (64 / 6 * Real.exp 4 + 16 * Real.exp 36) * Real.exp 4

theorem K3_pos : 0 < K3 := by unfold K3; positivity

instance gauss_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (gauss N) := by
  unfold gauss; infer_instance

theorem trace_mul_entries {N : ℕ} (W A : Mat N) :
    Matrix.trace (W * A) = ∑ a, ∑ b, W a b * A b a := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem trace_four_entries {N : ℕ} (W A C : Mat N) :
    Matrix.trace (W * A * W * C) = ∑ a, ∑ e, ∑ c, ∑ b, W a b * A b c * W c e * C e a := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]

/-! ### Continuity -/
theorem continuous_gMat {N : ℕ} : Continuous (fun w : Fin N × Fin N → ℝ => gMat w) := by
  unfold gMat
  have h1 : Continuous (fun w : Fin N × Fin N → ℝ => (Matrix.of fun a b => w (a, b) : Mat N)) :=
    continuous_matrix fun a b => continuous_apply (a, b)
  have h2 : Continuous (fun w : Fin N × Fin N → ℝ => (Matrix.of fun a b => w (b, a) : Mat N)) :=
    continuous_matrix fun a b => continuous_apply (b, a)
  have h3 : Continuous (fun w : Fin N × Fin N → ℝ =>
      (pMat N * (Matrix.of (fun a b => w (a, b)) + Matrix.of (fun a b => w (b, a))) * pMat N :
        Mat N)) :=
    (continuous_const.matrix_mul (h1.add h2)).matrix_mul continuous_const
  exact h3.const_smul (Real.sqrt ((N : ℝ) - 1))⁻¹

theorem continuous_Ft_gMat {N : ℕ} (θ : ℝ) (n : ℕ) (M : Mat N) :
    Continuous (fun w : Fin N × Fin N → ℝ => Ft θ n (M + gMat w)) := by
  unfold Ft Fn
  have h : Continuous (fun w : Fin N × Fin N → ℝ => (1 + (θ / (n : ℝ)) • (M + gMat w) : Mat N)) :=
    continuous_const.add
      ((continuous_const.add continuous_gMat :
        Continuous (fun w : Fin N × Fin N → ℝ => (M + gMat w : Mat N))).const_smul (θ / (n : ℝ)))
  exact ((h.pow n).matrix_trace).add continuous_const

/-! ### First-order terms -/
theorem sum_linTerm {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) (n : ℕ) (M : Mat N) :
    ∑ τ : Equiv.Perm (Fin N), linTerm θ n M (xMat τ) = 0 := by
  unfold linTerm
  rw [← Finset.mul_sum]
  simp only [trace_mul_entries]
  rw [Finset.sum_comm]
  have h : ∀ a : Fin N, ∑ τ : Equiv.Perm (Fin N), ∑ b,
      xMat τ a b * ((1 + (θ / (n : ℝ)) • M) ^ (n - 1)) b a = 0 := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul, sum_xMat hN, zero_mul]
  simp [h]

theorem integrable_trace_mul {N : ℕ} (A : Mat N) :
    Integrable (fun w => Matrix.trace (gMat w * A)) (gauss N) := by
  simp only [trace_mul_entries]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_gMat a b).mul_const _

theorem integral_trace_mul {N : ℕ} (A : Mat N) :
    ∫ w, Matrix.trace (gMat w * A) ∂gauss N = 0 := by
  simp only [trace_mul_entries]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_gMat a b).mul_const _]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (integrable_gMat a b).mul_const _]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [integral_mul_const, integral_gMat, zero_mul]

theorem integrable_linTerm {N : ℕ} (θ : ℝ) (n : ℕ) (M : Mat N) :
    Integrable (fun w => linTerm θ n M (gMat w)) (gauss N) := by
  unfold linTerm
  exact (integrable_trace_mul _).const_mul _

theorem integral_linTerm {N : ℕ} (θ : ℝ) (n : ℕ) (M : Mat N) :
    ∫ w, linTerm θ n M (gMat w) ∂gauss N = 0 := by
  unfold linTerm
  rw [integral_const_mul, integral_trace_mul, mul_zero]

/-! ### Second-order terms -/
theorem sum_trace_four {N : ℕ} (hN : 2 ≤ N) (A C : Mat N) :
    ∑ τ : Equiv.Perm (Fin N), Matrix.trace (xMat τ * A * xMat τ * C) =
      (N.factorial : ℝ) * ∑ a, ∑ e, ∑ c, ∑ b, cov N a b c e * (A b c * C e a) := by
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  simp only [trace_four_entries]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := sum_xMat_mul hN a b c e
  rw [div_eq_iff hfact.ne'] at h
  unfold cov
  rw [← mul_assoc, mul_comm (N.factorial : ℝ), ← h, Finset.sum_mul]
  exact Finset.sum_congr rfl fun τ _ => by ring

theorem trace_four_gMat {N : ℕ} (A C : Mat N) (w : Fin N × Fin N → ℝ) :
    Matrix.trace (gMat w * A * gMat w * C) =
      ∑ a, ∑ e, ∑ c, ∑ b, gMat w a b * gMat w c e * (A b c * C e a) := by
  rw [trace_four_entries]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

theorem integrable_trace_four {N : ℕ} (A C : Mat N) :
    Integrable (fun w => Matrix.trace (gMat w * A * gMat w * C)) (gauss N) := by
  simp only [trace_four_gMat]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun e _ =>
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ =>
      (integrable_gMat_mul a b c e).mul_const _

theorem integral_trace_four {N : ℕ} (hN : 2 ≤ N) (A C : Mat N) :
    ∫ w, Matrix.trace (gMat w * A * gMat w * C) ∂gauss N =
      ∑ a, ∑ e, ∑ c, ∑ b, cov N a b c e * (A b c * C e a) := by
  simp only [trace_four_gMat]
  have hi : ∀ a e c b : Fin N,
      Integrable (fun w => gMat w a b * gMat w c e * (A b c * C e a)) (gauss N) :=
    fun a e c b => (integrable_gMat_mul a b c e).mul_const _
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun e _ =>
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hi a e c b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun e _ =>
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hi a e c b]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hi a e c b]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun b _ => hi a e c b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_gMat_mul hN]
  rfl

theorem sum_quadTerm {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) (n : ℕ) (M : Mat N) :
    ∑ τ : Equiv.Perm (Fin N), quadTerm θ n M (xMat τ) = (N.factorial : ℝ) * qExpr θ n M := by
  unfold quadTerm qExpr
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [sum_trace_four hN]
  rw [← Finset.mul_sum]
  ring

theorem integrable_quadTerm {N : ℕ} (θ : ℝ) (n : ℕ) (M : Mat N) :
    Integrable (fun w => quadTerm θ n M (gMat w)) (gauss N) := by
  unfold quadTerm
  exact (integrable_finsetSum _ fun k _ => integrable_trace_four _ _).const_mul _

theorem integral_quadTerm {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) (n : ℕ) (M : Mat N) :
    ∫ w, quadTerm θ n M (gMat w) ∂gauss N = qExpr θ n M := by
  unfold quadTerm qExpr
  rw [integral_const_mul, integral_finsetSum _ fun k _ => integrable_trace_four _ _]
  simp only [integral_trace_four hN]

end StrongConv.T38.PartS
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartF
/-!
# T38 Part F: the chain of `d` Lindeberg swaps

`exists_chain`, by induction on `d` with a general symmetric base matrix `M`.
-/
instance gauss_isProb (N : ℕ) : IsProbabilityMeasure (gauss N) := by
  unfold gauss; infer_instance

instance gaussPow_isProb (d N : ℕ) : IsProbabilityMeasure (gaussPow d N) := by
  unfold gaussPow; infer_instance

theorem gSum_isHermitian {d N : ℕ} (w : Fin d → Fin N × Fin N → ℝ) : (gSum w).IsHermitian := by
  unfold gSum Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => (gMat_isHermitian (w i)).eq

theorem continuous_gMat {N : ℕ} : Continuous (fun w : Fin N × Fin N → ℝ => gMat w) := by
  unfold gMat
  have h : Continuous (fun w : Fin N × Fin N → ℝ =>
      pMat N * (Matrix.of (fun a b => w (a, b)) + Matrix.of (fun a b => w (b, a))) * pMat N) := by
    refine Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
    refine Continuous.add ?_ ?_
    · exact continuous_matrix fun a b => continuous_apply (a, b)
    · exact continuous_matrix fun a b => continuous_apply (b, a)
  exact h.const_smul (Real.sqrt ((N : ℝ) - 1))⁻¹

theorem continuous_gSum {d N : ℕ} :
    Continuous (fun w : Fin d → Fin N × Fin N → ℝ => gSum w) := by
  unfold gSum
  exact continuous_finsetSum _ fun i _ => continuous_gMat.comp (continuous_apply i)

theorem continuous_Ft {N : ℕ} (θ : ℝ) (n : ℕ) : Continuous (fun M : Mat N => Ft θ n M) := by
  unfold Ft Fn
  refine Continuous.add ?_ continuous_const
  refine Continuous.matrix_trace ?_
  exact ((continuous_const (y := (1 : Mat N))).add
    ((continuous_id (X := Mat N)).const_smul (θ / (n : ℝ)))).pow n

end StrongConv.T38.PartF
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartG
open StrongConv.T38
/-!
# T38 Part G: the tail bound for `‖xSum σ‖`
-/
instance instProbGauss (N : ℕ) : IsProbabilityMeasure (gauss N) := by
  unfold gauss; infer_instance

instance instProbGaussPow (d N : ℕ) : IsProbabilityMeasure (gaussPow d N) := by
  unfold gaussPow; infer_instance

theorem xSum_isHermitian {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : (xSum σ).IsHermitian := by
  unfold xSum Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => StrongConv.T38.xMat_isHermitian (σ i)

theorem gSum_isHermitian {d N : ℕ} (w : Fin d → Fin N × Fin N → ℝ) : (gSum w).IsHermitian := by
  unfold gSum Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => StrongConv.T38.gMat_isHermitian (w i)

/-- The exponent in the Gaussian norm bound of Part E. -/
def bexp (N d : ℕ) (θ : ℝ) : ℝ :=
  θ * (2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) + 6 * Real.sqrt (d / ((N : ℝ) - 1))) +
    4 * θ ^ 2 * d / ((N : ℝ) - 1)

theorem bexp_nonneg {N : ℕ} (hN : 2 ≤ N) (d : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) : 0 ≤ bexp N d θ := by
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold bexp
  have h1 : 0 ≤ Real.sqrt (2 * d * N / ((N : ℝ) - 1)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (d / ((N : ℝ) - 1)) := Real.sqrt_nonneg _
  have h3 : 0 ≤ 4 * θ ^ 2 * d / ((N : ℝ) - 1) := by positivity
  have h4 : 0 ≤ θ * (2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) +
      6 * Real.sqrt (d / ((N : ℝ) - 1))) := by positivity
  linarith

end StrongConv.T38.PartG
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartH
/-!
# T38, Part H: a real matrix and its complexification have the same `ℓ²` operator norm
-/
/-- The real part of a complex vector. -/
def reVec {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun i => (x i).re

/-- The imaginary part of a complex vector. -/
def imVec {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun i => (x i).im

/-- The complexification of a real vector. -/
def cVec {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun i => ((x i : ℝ) : ℂ)

theorem norm_sq_eq_re_add_im {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) :
    ‖x‖ ^ 2 = ‖reVec x‖ ^ 2 + ‖imVec x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [reVec, imVec, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_cVec {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) : ‖cVec x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [cVec]

theorem toE_map_apply {N : ℕ} (A : Mat N) (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    toEuclideanCLM (𝕜 := ℂ) (A.map (algebraMap ℝ ℂ)) x i = ∑ j, (A i j : ℂ) * x j := by
  have h : WithLp.ofLp (toEuclideanCLM (𝕜 := ℂ) (A.map (algebraMap ℝ ℂ)) x) i =
      ((A.map (algebraMap ℝ ℂ)) *ᵥ WithLp.ofLp x) i := by
    rw [ofLp_toEuclideanCLM]
  rw [h]
  simp [Matrix.mulVec, dotProduct]

theorem toE_real_apply {N : ℕ} (A : Mat N) (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    toEuclideanCLM (𝕜 := ℝ) A x i = ∑ j, A i j * x j := by
  have h : WithLp.ofLp (toEuclideanCLM (𝕜 := ℝ) A x) i = (A *ᵥ WithLp.ofLp x) i := by
    rw [ofLp_toEuclideanCLM]
  rw [h]
  simp [Matrix.mulVec, dotProduct]

theorem reVec_toE {N : ℕ} (A : Mat N) (x : EuclideanSpace ℂ (Fin N)) :
    reVec (toEuclideanCLM (𝕜 := ℂ) (A.map (algebraMap ℝ ℂ)) x) =
      toEuclideanCLM (𝕜 := ℝ) A (reVec x) := by
  ext i
  rw [toE_real_apply]
  simp only [reVec]
  rw [toE_map_apply, Complex.re_sum]
  simp

theorem imVec_toE {N : ℕ} (A : Mat N) (x : EuclideanSpace ℂ (Fin N)) :
    imVec (toEuclideanCLM (𝕜 := ℂ) (A.map (algebraMap ℝ ℂ)) x) =
      toEuclideanCLM (𝕜 := ℝ) A (imVec x) := by
  ext i
  rw [toE_real_apply]
  simp only [imVec]
  rw [toE_map_apply, Complex.im_sum]
  simp

theorem toE_cVec {N : ℕ} (A : Mat N) (x : EuclideanSpace ℝ (Fin N)) :
    toEuclideanCLM (𝕜 := ℂ) (A.map (algebraMap ℝ ℂ)) (cVec x) =
      cVec (toEuclideanCLM (𝕜 := ℝ) A x) := by
  ext i
  rw [toE_map_apply]
  simp only [cVec]
  rw [toE_real_apply]
  simp

/-- A real matrix and its complexification have the same `ℓ²` operator norm. -/
theorem norm_toEuclideanCLM_map_ofReal {N : ℕ} (A : Mat N) :
    ‖toEuclideanCLM (𝕜 := ℂ) (A.map (algebraMap ℝ ℂ))‖ = ‖A‖ := by
  rw [Matrix.cstar_norm_def A]
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    set a := ‖toEuclideanCLM (𝕜 := ℝ) A‖
    have ha : 0 ≤ a := norm_nonneg _
    have h1 : ‖toEuclideanCLM (𝕜 := ℝ) A (reVec x)‖ ≤ a * ‖reVec x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖toEuclideanCLM (𝕜 := ℝ) A (imVec x)‖ ≤ a * ‖imVec x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
    rw [norm_sq_eq_re_add_im, reVec_toE, imVec_toE, mul_pow, norm_sq_eq_re_add_im x, mul_add]
    have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow] at h1' h2'
    exact add_le_add h1' h2'
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [← norm_cVec, ← toE_cVec, ← norm_cVec x]
    exact ContinuousLinearMap.le_opNorm _ _

end StrongConv.T38.PartH
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part H: back to the complex matrices of the published reduction -/
alias norm_toEuclideanCLM_map_ofReal := StrongConv.T38.PartH.norm_toEuclideanCLM_map_ofReal

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartE
/-!
# T38 Part E, file 1: linear forms of a standard Gaussian vector

Generic facts about `Measure.pi fun _ : ι => gaussianReal 0 1`: second moments of linear forms,
the Sudakov–Fernique comparison for finite families of linear forms, and an exponential-moment
bound for Lipschitz functions derived from Gaussian concentration.
-/
/-- The standard Gaussian measure on `ι → ℝ`. -/
abbrev std (ι : Type*) [Fintype ι] : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1

/-- The linear form with coefficients `c`. -/
def lin {ι : Type*} [Fintype ι] (c : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ j, c j * x j

theorem inner_hSum {d N : ℕ} (y : Fin d × (Fin N × Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    inner ℝ x (toEuclideanCLM (𝕜 := ℝ) (hSum (Function.curry y)) x) = lin (cvec d x) y := by
  rw [inner_toEuclideanCLM]
  simp only [dotProduct, mulVec, hSum, Matrix.sum_apply, Matrix.add_apply, Matrix.of_apply,
    Function.curry_apply, lin, cvec, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    mul_add, add_mul, Finset.sum_add_distrib]
  have e1 : ∀ F : Fin N → Fin N → Fin d → ℝ,
      ∑ a, ∑ b, ∑ i, F a b i = ∑ i, ∑ a, ∑ b, F a b i := by
    intro F
    calc ∑ a, ∑ b, ∑ i, F a b i = ∑ a, ∑ i, ∑ b, F a b i :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, F a b i := Finset.sum_comm
  rw [e1 (fun a b i => x.ofLp a * (y (i, a, b) * x.ofLp b)),
    e1 (fun a b i => x.ofLp a * (y (i, b, a) * x.ofLp b)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (f := fun a b => x.ofLp a * (y (i, b, a) * x.ofLp b)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem sum_sq_sub {N : ℕ} (x y : Fin N → ℝ) :
    ∑ a, ∑ b, (x a * x b - y a * y b) ^ 2 =
      (∑ a, x a ^ 2) ^ 2 + (∑ a, y a ^ 2) ^ 2 - 2 * (∑ a, x a * y a) ^ 2 := by
  have h1 : (∑ a, x a ^ 2) ^ 2 = ∑ a, ∑ b, x a ^ 2 * x b ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
  have h2 : (∑ a, y a ^ 2) ^ 2 = ∑ a, ∑ b, y a ^ 2 * y b ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
  have h3 : (∑ a, x a * y a) ^ 2 = ∑ a, ∑ b, x a * y a * (x b * y b) := by
    rw [pow_two, Finset.sum_mul_sum]
  rw [h1, h2, h3, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem sum_cvec_sub_sq (d : ℕ) {N : ℕ} (s : ℝ) (hs : s ^ 2 = 1)
    (x y : EuclideanSpace ℝ (Fin N)) :
    ∑ j, (s * cvec d x j - s * cvec d y j) ^ 2 =
      4 * d * ((∑ a, x a ^ 2) ^ 2 + (∑ a, y a ^ 2) ^ 2 - 2 * (∑ a, x a * y a) ^ 2) := by
  rw [← sum_sq_sub (fun a => x a) (fun a => y a)]
  simp only [cvec, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [mul_comm (4 : ℝ) (d : ℝ), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : (s * (2 * x a * x b) - s * (2 * y a * y b)) ^ 2 =
      s ^ 2 * (4 * (x a * x b - y a * y b) ^ 2) := by ring
  rw [this, hs, one_mul]

theorem sum_cvec_sq (d : ℕ) {N : ℕ} (s : ℝ) (hs : s ^ 2 = 1) (x : EuclideanSpace ℝ (Fin N)) :
    ∑ j, (s * cvec d x j) ^ 2 = 4 * d * (∑ a, x a ^ 2) ^ 2 := by
  have h := sum_cvec_sub_sq d s hs x 0
  simpa [cvec] using h

/-! ### The supremum over a dense sequence of the sphere -/
/-- The unit sphere of `ℝ^N`. -/
abbrev Sph (N : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

theorem sum_sq_sph {N : ℕ} (x : Sph N) : ∑ a, x.1 a ^ 2 = 1 := by
  have h : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have h2 := EuclideanSpace.norm_sq_eq x.1
  rw [h] at h2
  simpa using h2.symm

/-- The maximum of the first `n + 1` signed quadratic forms `s ⟨u_k, H u_k⟩`. -/
def fsup (d : ℕ) {N : ℕ} (u : ℕ → Sph N) (s : ℝ) (n : ℕ) (y : Fin d × (Fin N × Fin N) → ℝ) : ℝ :=
  ⨆ k : Fin (n + 1), lin (fun j => s * cvec d (u k).1 j) y

end StrongConv.T38.PartE
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartE
variable {ι : Type*} [Fintype ι]
theorem isGaussian_std : IsGaussian (std ι) := by
  have h (i : ι) : HasGaussianLaw (fun x : ι → ℝ => x i) (std ι) := by
    refine ⟨?_⟩
    rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq]
    infer_instance
  have hi : iIndepFun (fun i (x : ι → ℝ) => x i) (std ι) :=
    iIndepFun_pi fun i => measurable_id.aemeasurable
  have hh := hi.hasGaussianLaw h
  have hh' : IsGaussian ((std ι).map id) := hh.isGaussian_map
  simpa only [Measure.map_id] using hh'

theorem memLp_coord (j : ι) : MemLp (fun x : ι → ℝ => x j) 2 (std ι) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) j)

theorem integrable_coord (j : ι) : Integrable (fun x : ι → ℝ => x j) (std ι) :=
  (memLp_coord j).integrable (by norm_num)

theorem integral_coord (j : ι) : ∫ x : ι → ℝ, x j ∂std ι = 0 := by
  have h := integral_map (μ := std ι) (φ := fun x : ι → ℝ => x j) (f := fun y : ℝ => y)
    (measurable_pi_apply j).aemeasurable measurable_id.aestronglyMeasurable
  rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 1) j).map_eq] at h
  rw [← h]
  exact integral_id_gaussianReal

theorem integrable_coord_mul (j l : ι) : Integrable (fun x : ι → ℝ => x j * x l) (std ι) :=
  (memLp_coord j).integrable_mul (memLp_coord l)

theorem integral_coord_mul [DecidableEq ι] (j l : ι) :
    ∫ x : ι → ℝ, x j * x l ∂std ι = if j = l then 1 else 0 := by
  split_ifs with hjl
  · subst hjl
    have h := integral_map (μ := std ι) (φ := fun x : ι → ℝ => x j) (f := fun y : ℝ => y * y)
      (measurable_pi_apply j).aemeasurable (by fun_prop)
    rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 1) j).map_eq] at h
    rw [← h]
    have hv := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero measurable_id.aemeasurable
      (by simpa using integral_id_gaussianReal (μ := 0) (v := 1))] at hv
    simpa [pow_two] using hv
  · have hi : iIndepFun (fun i (x : ι → ℝ) => x i) (std ι) :=
      iIndepFun_pi fun i => measurable_id.aemeasurable
    have h2 := (hi.indepFun hjl).integral_mul_eq_mul_integral
      (measurable_pi_apply j).aestronglyMeasurable (measurable_pi_apply l).aestronglyMeasurable
    have h3 : ∫ x : ι → ℝ, x j * x l ∂std ι = (∫ x : ι → ℝ, x j ∂std ι) * ∫ x : ι → ℝ, x l ∂std ι :=
      h2
    rw [h3, integral_coord, zero_mul]

theorem integral_lin (c : ι → ℝ) : ∫ x, lin c x ∂std ι = 0 := by
  unfold lin
  rw [integral_finsetSum _ fun j _ => (integrable_coord j).const_mul _]
  simp [integral_const_mul, integral_coord]

theorem lin_sq (c : ι → ℝ) (x : ι → ℝ) :
    lin c x ^ 2 = ∑ j, ∑ l, c j * c l * (x j * x l) := by
  unfold lin
  rw [pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem integral_lin_sq (c : ι → ℝ) : ∫ x, lin c x ^ 2 ∂std ι = ∑ j, c j ^ 2 := by
  classical
  simp_rw [lin_sq]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    (integrable_coord_mul j l).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => (integrable_coord_mul j l).const_mul _]
  simp_rw [integral_const_mul, integral_coord_mul]
  simp [pow_two]

theorem lin_sub (c c' : ι → ℝ) (x : ι → ℝ) : lin c x - lin c' x = lin (fun j => c j - c' j) x := by
  unfold lin
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem lin_sub_right (c : ι → ℝ) (x y : ι → ℝ) :
    lin c x - lin c y = lin c (fun j => x j - y j) := by
  unfold lin
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem abs_lin_le (c : ι → ℝ) (x : ι → ℝ) :
    |lin c x| ≤ Real.sqrt (∑ j, c j ^ 2) * Real.sqrt (∑ j, x j ^ 2) := by
  rw [abs_le]
  constructor
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => -c j) x
    simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h
    unfold lin
    linarith
  · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ c x

/-- A finite supremum of linear forms with coefficient norm at most `L` is `L`-Lipschitz. -/
theorem abs_iSup_lin_sub_le {κ : Type*} [Finite κ] [Nonempty κ] (c : κ → ι → ℝ) (L : ℝ)
    (hc : ∀ k, Real.sqrt (∑ j, c k j ^ 2) ≤ L) (x y : ι → ℝ) :
    |(⨆ k, lin (c k) x) - ⨆ k, lin (c k) y| ≤ L * Real.sqrt (∑ j, (x j - y j) ^ 2) := by
  have key : ∀ x y : ι → ℝ, (⨆ k, lin (c k) x) ≤
      (⨆ k, lin (c k) y) + L * Real.sqrt (∑ j, (x j - y j) ^ 2) := by
    intro x y
    refine ciSup_le fun k => ?_
    have h1 : lin (c k) y ≤ ⨆ k, lin (c k) y := le_ciSup (f := fun k => lin (c k) y) (Finite.bddAbove_range _) k
    have h2 := abs_lin_le (c k) (fun j => x j - y j)
    rw [← lin_sub_right] at h2
    have h3 : Real.sqrt (∑ j, c k j ^ 2) * Real.sqrt (∑ j, (x j - y j) ^ 2) ≤
        L * Real.sqrt (∑ j, (x j - y j) ^ 2) :=
      mul_le_mul_of_nonneg_right (hc k) (Real.sqrt_nonneg _)
    have h4 := (abs_le.mp h2).2
    linarith
  rw [abs_sub_le_iff]
  constructor
  · have := key x y
    linarith
  · have := key y x
    have e : ∑ j, (y j - x j) ^ 2 = ∑ j, (x j - y j) ^ 2 :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [e] at this
    linarith

theorem hasGaussianLaw_lin {κ : Type*} [Fintype κ] (c : κ → ι → ℝ) :
    HasGaussianLaw (fun (x : ι → ℝ) (k : κ) => lin (c k) x) (std ι) := by
  have : IsGaussian (std ι) := isGaussian_std
  let Lm : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
    ContinuousLinearMap.pi fun k => ∑ j, c k j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j
  have h := (IsGaussian.hasGaussianLaw_id (μ := std ι)).map_fun Lm
  have e : (fun x : ι → ℝ => Lm (id x)) = fun (x : ι → ℝ) (k : κ) => lin (c k) x := by
    funext x k
    simp [Lm, lin]
  rw [e] at h
  exact h

/-- Sudakov–Fernique for two finite families of linear forms of standard Gaussian vectors. -/
theorem integral_iSup_lin_le {ι' κ : Type*} [Fintype ι'] [Fintype κ] (c : κ → ι → ℝ)
    (c' : κ → ι' → ℝ)
    (h : ∀ k l, ∑ j, (c k j - c l j) ^ 2 ≤ ∑ j, (c' k j - c' l j) ^ 2) :
    ∫ x, (⨆ k, lin (c k) x) ∂std ι ≤ ∫ x, (⨆ k, lin (c' k) x) ∂std ι' := by
  refine GaussianMatrix.sudakov_fernique (fun k x => lin (c k) x) (fun k x => lin (c' k) x)
    (hasGaussianLaw_lin c) (hasGaussianLaw_lin c') (fun k => integral_lin _)
    (fun k => integral_lin _) fun k l => ?_
  simp_rw [lin_sub, integral_lin_sq]
  exact h k l

theorem integral_sum_sq : ∫ x : ι → ℝ, ∑ j, x j ^ 2 ∂std ι = Fintype.card ι := by
  classical
  rw [integral_finsetSum _ fun j _ => by simpa [pow_two] using integrable_coord_mul j j]
  have : ∀ j : ι, ∫ x : ι → ℝ, x j ^ 2 ∂std ι = 1 := fun j => by
    simpa [pow_two] using integral_coord_mul j j
  simp [this]

/-- `E sup_k ⟨c_k, g⟩ ≤ D √n` when every `c_k` has norm at most `D`. -/
theorem integral_iSup_lin_le_sqrt {κ : Type*} [Finite κ] [Nonempty κ] [Nonempty ι]
    (c : κ → ι → ℝ) (D : ℝ) (hD : 0 ≤ D) (hc : ∀ k, Real.sqrt (∑ j, c k j ^ 2) ≤ D) :
    ∫ x, (⨆ k, lin (c k) x) ∂std ι ≤ D * Real.sqrt (Fintype.card ι) := by
  set r : ℝ := Real.sqrt (Fintype.card ι) with hr
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hrpos : 0 < r := Real.sqrt_pos.mpr hcard
  have hrr : r * r = Fintype.card ι := Real.mul_self_sqrt hcard.le
  by_cases hint : Integrable (fun x => ⨆ k, lin (c k) x) (std ι)
  · have hint2 : Integrable (fun x : ι → ℝ => D * (((∑ j, x j ^ 2) / r + r) / 2)) (std ι) := by
      have : Integrable (fun x : ι → ℝ => ∑ j, x j ^ 2) (std ι) :=
        integrable_finsetSum _ fun j _ => by simpa [pow_two] using integrable_coord_mul j j
      exact (((this.div_const r).add (integrable_const r)).div_const 2).const_mul D
    have hpt : ∀ x : ι → ℝ, (⨆ k, lin (c k) x) ≤ D * (((∑ j, x j ^ 2) / r + r) / 2) := by
      intro x
      refine ciSup_le fun k => ?_
      have h1 := (abs_le.mp (abs_lin_le (c k) x)).2
      have hs : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      set S := ∑ j, x j ^ 2 with hS
      have h2 : Real.sqrt S ≤ (S / r + r) / 2 := by
        have hsq : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hs
        have h3 : 0 ≤ (Real.sqrt S - r) ^ 2 := sq_nonneg _
        have h4 : S / r = Real.sqrt S * Real.sqrt S / r := by rw [hsq]
        rw [h4, div_add' _ _ _ hrpos.ne', le_div_iff₀ (by positivity), le_div_iff₀ hrpos]
        nlinarith
      calc lin (c k) x ≤ Real.sqrt (∑ j, c k j ^ 2) * Real.sqrt S := h1
        _ ≤ D * Real.sqrt S := mul_le_mul_of_nonneg_right (hc k) (Real.sqrt_nonneg _)
        _ ≤ D * ((S / r + r) / 2) := mul_le_mul_of_nonneg_left h2 hD
    calc ∫ x, (⨆ k, lin (c k) x) ∂std ι
        ≤ ∫ x : ι → ℝ, D * (((∑ j, x j ^ 2) / r + r) / 2) ∂std ι :=
          integral_mono hint hint2 hpt
      _ = D * (((Fintype.card ι : ℝ) / r + r) / 2) := by
          have : Integrable (fun x : ι → ℝ => ∑ j, x j ^ 2) (std ι) :=
            integrable_finsetSum _ fun j _ => by simpa [pow_two] using integrable_coord_mul j j
          rw [integral_const_mul, integral_div, integral_add (this.div_const r) (integrable_const r),
            integral_div, integral_sum_sq]
          simp
      _ = D * r := by
          rw [← hrr]
          field_simp
          ring
  · rw [integral_undef hint]
    positivity

/-- Exponential moments of a Lipschitz function of a standard Gaussian vector, from Gaussian
concentration: `E e^{θ f} ≤ 6 exp(θ m + θ L + θ² L²)` whenever `E f ≤ m`. -/
theorem lintegral_exp_le (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (m : ℝ)
    (hm : ∫ x, f x ∂std ι ≤ m) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (θ * f x)) ∂std ι ≤
      ENNReal.ofReal (6 * Real.exp (θ * m + θ * L + θ ^ 2 * L ^ 2)) := by
  have hconc := fun k : ℕ =>
    GaussianMatrix.gaussian_concentration_vector f L hL hLip (k : ℝ) (Nat.cast_nonneg k)
  have hfint : Integrable f (std ι) := (hconc 0).1
  have hfm : AEMeasurable f (std ι) := hfint.aemeasurable
  set a : ℝ := θ * L with ha
  have ha0 : 0 ≤ a := mul_nonneg hθ hL.le
  let T : ℕ → Set (ι → ℝ) := fun k => {x | (∫ y, f y ∂std ι) + L * k ≤ f x}
  have hT : ∀ k, NullMeasurableSet (T k) (std ι) := fun k =>
    hfm.nullMeasurable measurableSet_Ici
  let g : ℕ → (ι → ℝ) → ENNReal := fun k =>
    (T k).indicator fun _ => ENNReal.ofReal (Real.exp (a * (k + 1)))
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (θ * f x)) ≤
      ENNReal.ofReal (Real.exp (θ * m)) * (1 + ∑' k, g k x) := by
    intro x
    by_cases hz : f x - m < 0
    · calc ENNReal.ofReal (Real.exp (θ * f x)) ≤ ENNReal.ofReal (Real.exp (θ * m)) * 1 := by
            rw [mul_one]
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
            nlinarith
        _ ≤ _ := by gcongr; exact le_self_add
    · rw [not_lt] at hz
      set k₀ : ℕ := ⌊(f x - m) / L⌋₊ with hk
      have h1 : (k₀ : ℝ) ≤ (f x - m) / L := Nat.floor_le (div_nonneg hz hL.le)
      have h2 : (f x - m) / L < k₀ + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hL] at h1
      rw [div_lt_iff₀ hL] at h2
      have hx : x ∈ T k₀ := by
        change (∫ y, f y ∂std ι) + L * k₀ ≤ f x
        linarith
      have hg : g k₀ x = ENNReal.ofReal (Real.exp (a * (k₀ + 1))) := by
        simp only [g]
        rw [Set.indicator_of_mem hx]
      calc ENNReal.ofReal (Real.exp (θ * f x))
          ≤ ENNReal.ofReal (Real.exp (θ * m) * Real.exp (a * (k₀ + 1))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            have : θ * (f x - m) ≤ θ * ((k₀ + 1) * L) := mul_le_mul_of_nonneg_left h2.le hθ
            rw [ha]
            linarith
        _ = ENNReal.ofReal (Real.exp (θ * m)) * g k₀ x := by
            rw [hg, ENNReal.ofReal_mul (Real.exp_pos _).le]
        _ ≤ _ := by
            gcongr
            exact (ENNReal.le_tsum k₀).trans le_add_self
  set C : ℝ := Real.exp (a + a ^ 2) with hC
  set r : ℝ := Real.exp (-(1 / 4)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 4 / 5 := by
    have h1 : (5 : ℝ) / 4 ≤ Real.exp (1 / 4) := by
      have := Real.add_one_le_exp (1 / 4 : ℝ)
      linarith
    rw [hrdef, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hgk : ∀ k : ℕ, ∫⁻ x, g k x ∂std ι ≤ ENNReal.ofReal (C * r ^ k) := by
    intro k
    simp only [g]
    rw [lintegral_indicator₀ (hT k), setLIntegral_const]
    calc ENNReal.ofReal (Real.exp (a * (k + 1))) * (std ι) (T k)
        ≤ ENNReal.ofReal (Real.exp (a * (k + 1))) * ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) := by
          gcongr
          exact (hconc k).2
      _ = ENNReal.ofReal (Real.exp (a * (k + 1) + -(k : ℝ) ^ 2 / 2)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      _ ≤ ENNReal.ofReal (C * r ^ k) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hC, hrdef, ← Real.exp_nat_mul, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have hk1 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
            have : (k : ℝ) = 0 ∨ 1 ≤ (k : ℝ) := by
              rcases Nat.eq_zero_or_pos k with h | h
              · left; simp [h]
              · right; exact_mod_cast h
            rcases this with h | h
            · simp [h]
            · nlinarith
          nlinarith [sq_nonneg (a - k / 2)]
  have hsum : ∑' k : ℕ, ENNReal.ofReal (C * r ^ k) ≤ ENNReal.ofReal (5 * C) := by
    have hsm : Summable fun k : ℕ => C * r ^ k :=
      (summable_geometric_of_lt_one hr0 (by linarith)).mul_left C
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
    have h5 : (1 - r)⁻¹ ≤ 5 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hCpos : 0 < C := Real.exp_pos _
    nlinarith
  have hC1 : 1 ≤ C := by
    rw [hC]
    exact Real.one_le_exp (by positivity)
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (θ * f x)) ∂std ι
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (θ * m)) * (1 + ∑' k, g k x) ∂std ι :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (θ * m)) * (1 + ∑' k, ∫⁻ x, g k x ∂std ι) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          lintegral_tsum fun k => (aemeasurable_const.indicator₀ (hT k)), lintegral_one,
          measure_univ]
    _ ≤ ENNReal.ofReal (Real.exp (θ * m)) * (1 + ENNReal.ofReal (5 * C)) := by
        gcongr
        exact (ENNReal.tsum_le_tsum hgk).trans hsum
    _ ≤ ENNReal.ofReal (6 * Real.exp (θ * m + θ * L + θ ^ 2 * L ^ 2)) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        have e : θ * m + θ * L + θ ^ 2 * L ^ 2 = θ * m + (a + a ^ 2) := by rw [ha]; ring
        rw [e, Real.exp_add, ← hC]
        have := Real.exp_pos (θ * m)
        nlinarith

end StrongConv.T38.PartE
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartE
theorem lintegral_exp_fsup_le {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (u : ℕ → Sph N) (s : ℝ)
    (hs : s ^ 2 = 1) (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (θ * fsup d u s n y)) ∂std (Fin d × (Fin N × Fin N)) ≤
      ENNReal.ofReal (6 * Real.exp (θ * (Real.sqrt (8 * d) * Real.sqrt N) +
        θ * (2 * Real.sqrt d) + θ ^ 2 * (2 * Real.sqrt d) ^ 2)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hL : (0 : ℝ) < 2 * Real.sqrt d := by positivity
  refine lintegral_exp_le (fsup d u s n) _ hL ?_ _ ?_ θ hθ
  · intro x y
    refine abs_iSup_lin_sub_le _ _ (fun k => ?_) x y
    rw [sum_cvec_sq d s hs, sum_sq_sph]
    have : (4 : ℝ) * d * 1 ^ 2 = 2 ^ 2 * d := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    calc ∫ x, fsup d u s n x ∂std (Fin d × (Fin N × Fin N))
        ≤ ∫ g, (⨆ k : Fin (n + 1), lin (fun a => Real.sqrt (8 * d) * (u k).1 a) g) ∂std (Fin N) :=
          integral_iSup_lin_le _ _ (fun k l => ?_)
      _ ≤ Real.sqrt (8 * d) * Real.sqrt (Fintype.card (Fin N)) :=
          integral_iSup_lin_le_sqrt _ _ (Real.sqrt_nonneg _) (fun k => ?_)
      _ = _ := by simp
    · rw [sum_cvec_sub_sq d s hs, sum_sq_sph, sum_sq_sph]
      have h8 : Real.sqrt (8 * d) ^ 2 = 8 * d := Real.sq_sqrt (by positivity)
      have e : ∑ a, (Real.sqrt (8 * d) * (u k).1 a - Real.sqrt (8 * d) * (u l).1 a) ^ 2 =
          8 * d * (2 - 2 * ∑ a, (u k).1 a * (u l).1 a) := by
        have : ∀ a, (Real.sqrt (8 * d) * (u k).1 a - Real.sqrt (8 * d) * (u l).1 a) ^ 2 =
            8 * d * ((u k).1 a ^ 2 + (u l).1 a ^ 2 - 2 * ((u k).1 a * (u l).1 a)) := by
          intro a
          linear_combination ((u k).1 a - (u l).1 a) ^ 2 * h8
        simp_rw [this]
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_sq_sph,
          sum_sq_sph, ← Finset.mul_sum]
        ring
      rw [e]
      nlinarith [mul_nonneg hd0.le (sq_nonneg (1 - ∑ a, (u k).1 a * (u l).1 a))]
    · have : ∑ a, (Real.sqrt (8 * d) * (u k).1 a) ^ 2 = Real.sqrt (8 * d) ^ 2 * 1 := by
        simp_rw [mul_pow]
        rw [← Finset.mul_sum, sum_sq_sph]
      rw [this, mul_one, Real.sqrt_sq (Real.sqrt_nonneg _)]

theorem exists_sph_norm_le {N : ℕ} (hN : 1 ≤ N) (A : Mat N) (hA : A.IsHermitian) :
    ∃ x : Sph N, ‖A‖ ≤ |inner ℝ x.1 (toEuclideanCLM (𝕜 := ℝ) A x.1)| := by
  have hT : ((toEuclideanCLM (𝕜 := ℝ) (n := Fin N) A :
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
      EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1).Nonempty :=
    ⟨EuclideanSpace.single ⟨0, hN⟩ 1, by simp⟩
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).exists_isMaxOn hne
    (f := fun x => |inner ℝ x (toEuclideanCLM (𝕜 := ℝ) (n := Fin N) A x)|)
    (by fun_prop)
  refine ⟨⟨x₀, hx₀⟩, ?_⟩
  rw [Matrix.cstar_norm_def, ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hT]
  refine ciSup_le fun x => ?_
  by_cases hx : x = 0
  · subst hx
    simp
  · have hc : (‖x‖⁻¹ : ℝ) ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hx)
    rw [← ContinuousLinearMap.rayleigh_smul _ x hc]
    have hy : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
    have h := isMaxOn_iff.mp hmax _ (mem_sphere_zero_iff_norm.mpr hy)
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      hy, one_pow, div_one]
    rw [real_inner_comm] at h
    exact h

theorem ofReal_exp_norm_le {N : ℕ} (hN : 1 ≤ N) (u : ℕ → Sph N) (hu : DenseRange u) (A : Mat N)
    (hA : A.IsHermitian) (θ : ℝ) (hθ : 0 ≤ θ) (S : ENNReal)
    (hS : ∀ k, ENNReal.ofReal
      (Real.exp (θ * |inner ℝ (u k).1 (toEuclideanCLM (𝕜 := ℝ) A (u k).1)|)) ≤ S) :
    ENNReal.ofReal (Real.exp (θ * ‖A‖)) ≤ S := by
  obtain ⟨x, hx⟩ := exists_sph_norm_le hN A hA
  have hall : ∀ x : Sph N, ENNReal.ofReal
      (Real.exp (θ * |inner ℝ x.1 (toEuclideanCLM (𝕜 := ℝ) A x.1)|)) ≤ S := by
    intro x
    exact hu.induction_on x (isClosed_le (ENNReal.continuous_ofReal.comp (by fun_prop)) continuous_const) hS
  exact le_trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx hθ))) (hall x)

theorem measurable_lin {ι : Type*} [Fintype ι] (c : ι → ℝ) : Measurable (lin c) := by
  unfold lin
  fun_prop

theorem lintegral_exp_norm_hSum_le {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp
        (θ * ‖hSum (Function.curry y : Fin d → Fin N × Fin N → ℝ)‖))
        ∂std (Fin d × (Fin N × Fin N)) ≤
      ENNReal.ofReal (12 * Real.exp (θ * (Real.sqrt (8 * d) * Real.sqrt N) +
        θ * (2 * Real.sqrt d) + θ ^ 2 * (2 * Real.sqrt d) ^ 2)) := by
  have : Nonempty (Sph N) := ⟨⟨EuclideanSpace.single ⟨0, hN⟩ 1, by simp⟩⟩
  let u : ℕ → Sph N := TopologicalSpace.denseSeq (Sph N)
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq _
  let g : ℕ → (Fin d × (Fin N × Fin N) → ℝ) → ENNReal := fun n y =>
    ENNReal.ofReal (Real.exp (θ * fsup d u 1 n y)) +
      ENNReal.ofReal (Real.exp (θ * fsup d u (-1) n y))
  have hmeas_f : ∀ (s : ℝ) (n : ℕ), Measurable (fsup d u s n) := fun s n =>
    Measurable.iSup fun k => measurable_lin _
  have hmeas : ∀ (s : ℝ) (n : ℕ),
      Measurable fun y => ENNReal.ofReal (Real.exp (θ * fsup d u s n y)) := fun s n =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hmeas_f s n).const_mul θ))
  have hmono_f : ∀ (s : ℝ) (n : ℕ) (y : Fin d × (Fin N × Fin N) → ℝ),
      fsup d u s n y ≤ fsup d u s (n + 1) y := by
    intro s n y
    refine ciSup_le fun k => ?_
    exact le_ciSup (f := fun k : Fin (n + 1 + 1) => lin (fun j => s * cvec d (u k).1 j) y)
      (Finite.bddAbove_range _) k.castSucc
  have hmono : Monotone g := monotone_nat_of_le_succ fun n y => by
    simp only [g]
    exact add_le_add
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hmono_f 1 n y) hθ)))
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hmono_f (-1) n y) hθ)))
  have hpt : ∀ y : Fin d × (Fin N × Fin N) → ℝ, ENNReal.ofReal (Real.exp
      (θ * ‖hSum (Function.curry y : Fin d → Fin N × Fin N → ℝ)‖)) ≤ ⨆ n, g n y := by
    intro y
    refine ofReal_exp_norm_le hN u hu _ (hSum_isHermitian _) θ hθ _ fun k => ?_
    rw [inner_hSum]
    refine le_trans ?_ (le_iSup (fun n => g n y) k)
    have h1 : lin (cvec d (u k).1) y ≤ fsup d u 1 k y := by
      have := le_ciSup (f := fun i : Fin (k + 1) => lin (fun j => (1 : ℝ) * cvec d (u i).1 j) y)
        (Finite.bddAbove_range _) (Fin.last k)
      simpa [fsup] using this
    have h2 : -lin (cvec d (u k).1) y ≤ fsup d u (-1) k y := by
      have := le_ciSup (f := fun i : Fin (k + 1) => lin (fun j => (-1 : ℝ) * cvec d (u i).1 j) y)
        (Finite.bddAbove_range _) (Fin.last k)
      simpa [fsup, lin] using this
    rcases abs_cases (lin (cvec d (u k).1) y) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact le_trans (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1 hθ))) le_self_add
    · rw [h]
      exact le_trans (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 hθ))) le_add_self
  calc ∫⁻ y, ENNReal.ofReal (Real.exp
        (θ * ‖hSum (Function.curry y : Fin d → Fin N × Fin N → ℝ)‖))
        ∂std (Fin d × (Fin N × Fin N))
      ≤ ∫⁻ y, ⨆ n, g n y ∂std (Fin d × (Fin N × Fin N)) := lintegral_mono hpt
    _ = ⨆ n, ∫⁻ y, g n y ∂std (Fin d × (Fin N × Fin N)) :=
        lintegral_iSup (fun n => (hmeas 1 n).add (hmeas (-1) n)) hmono
    _ ≤ _ := by
        refine iSup_le fun n => ?_
        simp only [g]
        rw [lintegral_add_left (hmeas 1 n)]
        have h1 := lintegral_exp_fsup_le hd hN u 1 (by norm_num) n θ hθ
        have h2 := lintegral_exp_fsup_le hd hN u (-1) (by norm_num) n θ hθ
        refine (add_le_add h1 h2).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ### Transfer to `gaussPow` and the four statements -/
theorem measurePreserving_curry (d N : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin d) (Fin N × Fin N) ℝ)
      (std (Fin d × (Fin N × Fin N))) (gaussPow d N) := by
  refine ⟨(MeasurableEquiv.curry _ _ _).measurable, ?_⟩
  unfold gaussPow gauss
  simpa only [Measure.infinitePi_eq_pi] using
    Measure.infinitePi_map_curry (fun (_ : Fin d) (_ : Fin N × Fin N) => gaussianReal 0 1)

theorem continuous_norm_gSum {d N : ℕ} :
    Continuous fun w : Fin d → Fin N × Fin N → ℝ => ‖gSum w‖ := by
  unfold gSum gMat
  fun_prop

theorem lintegral_exp_norm_gSum_le {N : ℕ} (hN : 2 ≤ N) (d : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (θ * ‖gSum w‖)) ∂gaussPow d N ≤
      ENNReal.ofReal (16 * Real.exp (θ * (2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) +
        6 * Real.sqrt (d / ((N : ℝ) - 1))) + 4 * θ ^ 2 * d / ((N : ℝ) - 1))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsProbabilityMeasure (gaussPow 0 N) := by
      unfold gaussPow gauss
      infer_instance
    simp [gSum]
  · have hρ : 0 ≤ (Real.sqrt ((N : ℝ) - 1))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h1 : Real.sqrt (8 * d) * Real.sqrt N * (Real.sqrt ((N : ℝ) - 1))⁻¹ =
        2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) := by
      calc Real.sqrt (8 * d) * Real.sqrt N * (Real.sqrt ((N : ℝ) - 1))⁻¹
          = Real.sqrt (8 * d * N * ((N : ℝ) - 1)⁻¹) := by
            rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        _ = Real.sqrt (4 * (2 * d * N / ((N : ℝ) - 1))) := by
            congr 1
            ring
        _ = Real.sqrt 4 * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) := Real.sqrt_mul (by norm_num) _
        _ = _ := by rw [h4]
    have h3 : Real.sqrt d * (Real.sqrt ((N : ℝ) - 1))⁻¹ = Real.sqrt (d / ((N : ℝ) - 1)) := by
      rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), div_eq_mul_inv]
    have h5 : (Real.sqrt ((N : ℝ) - 1))⁻¹ ^ 2 = ((N : ℝ) - 1)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by linarith)]
    have hd2 : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
    rw [← (measurePreserving_curry d N).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    calc ∫⁻ y, ENNReal.ofReal (Real.exp
          (θ * ‖gSum (MeasurableEquiv.curry (Fin d) (Fin N × Fin N) ℝ y)‖))
          ∂std (Fin d × (Fin N × Fin N))
        ≤ ∫⁻ y, ENNReal.ofReal (Real.exp ((θ * (Real.sqrt ((N : ℝ) - 1))⁻¹) *
            ‖hSum (Function.curry y : Fin d → Fin N × Fin N → ℝ)‖))
            ∂std (Fin d × (Fin N × Fin N)) := by
          refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have h := norm_gSum_le (d := d) (by omega : 1 ≤ N) (Function.curry y)
          calc θ * ‖gSum (MeasurableEquiv.curry (Fin d) (Fin N × Fin N) ℝ y)‖
              ≤ θ * ((Real.sqrt ((N : ℝ) - 1))⁻¹ * ‖hSum (Function.curry y)‖) :=
                mul_le_mul_of_nonneg_left h hθ
            _ = _ := by ring
      _ ≤ _ := lintegral_exp_norm_hSum_le hd (by omega) _ (mul_nonneg hθ hρ)
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hE : θ * (Real.sqrt ((N : ℝ) - 1))⁻¹ * (Real.sqrt (8 * d) * Real.sqrt N) +
              θ * (Real.sqrt ((N : ℝ) - 1))⁻¹ * (2 * Real.sqrt d) +
              (θ * (Real.sqrt ((N : ℝ) - 1))⁻¹) ^ 2 * (2 * Real.sqrt d) ^ 2 =
              θ * (2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1))) +
              2 * θ * Real.sqrt (d / ((N : ℝ) - 1)) + 4 * θ ^ 2 * d / ((N : ℝ) - 1) := by
            rw [← h1, ← h3]
            have : (θ * (Real.sqrt ((N : ℝ) - 1))⁻¹) ^ 2 * (2 * Real.sqrt d) ^ 2 =
                4 * θ ^ 2 * ((Real.sqrt ((N : ℝ) - 1))⁻¹ ^ 2) * (Real.sqrt d ^ 2) := by ring
            rw [this, h5, hd2]
            ring
          rw [hE]
          have hB : 0 ≤ Real.sqrt ((d : ℝ) / ((N : ℝ) - 1)) := Real.sqrt_nonneg _
          have hle : θ * (2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1))) +
              2 * θ * Real.sqrt (d / ((N : ℝ) - 1)) + 4 * θ ^ 2 * d / ((N : ℝ) - 1) ≤
              θ * (2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) +
                6 * Real.sqrt (d / ((N : ℝ) - 1))) + 4 * θ ^ 2 * d / ((N : ℝ) - 1) := by
            nlinarith [mul_nonneg hθ hB]
          have := Real.exp_le_exp.mpr hle
          nlinarith [Real.exp_pos (θ * (2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1))) +
              2 * θ * Real.sqrt (d / ((N : ℝ) - 1)) + 4 * θ ^ 2 * d / ((N : ℝ) - 1))]

theorem integrable_exp_norm_gSum {N : ℕ} (hN : 2 ≤ N) (d : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun w : Fin d → Fin N × Fin N → ℝ => Real.exp (θ * ‖gSum w‖)) (gaussPow d N) := by
  have hc : Continuous fun w : Fin d → Fin N × Fin N → ℝ => Real.exp (θ * ‖gSum w‖) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_norm_gSum)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)]
  exact lt_of_le_of_lt (lintegral_exp_norm_gSum_le hN d θ hθ) ENNReal.ofReal_lt_top

end StrongConv.T38.PartE
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part E: the norm of the Gaussian model -/
alias integrable_exp_norm_gSum := StrongConv.T38.PartE.integrable_exp_norm_gSum

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartE
theorem integral_exp_norm_gSum_le {N : ℕ} (hN : 2 ≤ N) (d : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ w, Real.exp (θ * ‖gSum w‖) ∂gaussPow d N ≤
      16 * Real.exp (θ * (2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) +
        6 * Real.sqrt (d / ((N : ℝ) - 1))) + 4 * θ ^ 2 * d / ((N : ℝ) - 1)) := by
  have hc : Continuous fun w : Fin d → Fin N × Fin N → ℝ => Real.exp (θ * ‖gSum w‖) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_norm_gSum)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le) hc.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lintegral_exp_norm_gSum_le hN d θ hθ)

end StrongConv.T38.PartE
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias integral_exp_norm_gSum_le := StrongConv.T38.PartE.integral_exp_norm_gSum_le

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartE
theorem gSum_one {N : ℕ} (v : Fin 1 → Fin N × Fin N → ℝ) : gSum v = gMat (v 0) := by
  simp [gSum]

theorem integrable_exp_norm_gMat {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun w : Fin N × Fin N → ℝ => Real.exp (θ * ‖gMat w‖)) (gauss N) := by
  have mp := measurePreserving_funUnique (gauss N) (Fin 1)
  have h := integrable_exp_norm_gSum hN 1 θ hθ
  refine (mp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mp ?_
  have e : (fun w : Fin N × Fin N → ℝ => Real.exp (θ * ‖gMat w‖)) ∘
      (MeasurableEquiv.funUnique (Fin 1) (Fin N × Fin N → ℝ)) =
      fun w => Real.exp (θ * ‖gSum w‖) := by
    funext v
    simp only [Function.comp, gSum_one]
    rfl
  rw [e]
  exact h

end StrongConv.T38.PartE
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias integrable_exp_norm_gMat := StrongConv.T38.PartE.integrable_exp_norm_gMat

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartE
theorem integral_exp_norm_gMat_le {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ w, Real.exp (θ * ‖gMat w‖) ∂gauss N ≤
      16 * Real.exp (θ * (2 * Real.sqrt (2 * N / ((N : ℝ) - 1)) +
        6 * Real.sqrt (1 / ((N : ℝ) - 1))) + 4 * θ ^ 2 / ((N : ℝ) - 1)) := by
  have mp := measurePreserving_funUnique (gauss N) (Fin 1)
  have h := integral_exp_norm_gSum_le hN 1 θ hθ
  simp only [Nat.cast_one, mul_one] at h
  have e : ∫ w, Real.exp (θ * ‖gMat w‖) ∂gauss N =
      ∫ v, Real.exp (θ * ‖gSum v‖) ∂gaussPow 1 N := by
    rw [← mp.integral_comp' (fun w => Real.exp (θ * ‖gMat w‖))]
    simp only [gSum_one]
    rfl
  rw [e]
  exact h

end StrongConv.T38.PartE
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
alias integral_exp_norm_gMat_le := StrongConv.T38.PartE.integral_exp_norm_gMat_le

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartS
/-! ### The Gaussian moment bound -/
theorem integral_exp_two_le {N : ℕ} (hN : 2 ≤ N) :
    ∫ w, Real.exp (2 * ‖gMat w‖) ∂gauss N ≤ 16 * Real.exp 36 := by
  refine (integral_exp_norm_gMat_le hN 2 (by norm_num)).trans ?_
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have h1 : Real.sqrt (2 * N / ((N : ℝ) - 1)) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    rw [div_le_iff₀ hpos]; nlinarith
  have h2 : Real.sqrt (1 / ((N : ℝ) - 1)) ≤ 1 := by
    rw [Real.sqrt_le_left (by norm_num)]
    rw [div_le_iff₀ hpos]; nlinarith
  have h3 : 4 * (2 : ℝ) ^ 2 / ((N : ℝ) - 1) ≤ 16 := by
    rw [div_le_iff₀ hpos]; nlinarith
  have : (2 : ℝ) * (2 * Real.sqrt (2 * N / ((N : ℝ) - 1)) + 6 * Real.sqrt (1 / ((N : ℝ) - 1))) +
      4 * 2 ^ 2 / ((N : ℝ) - 1) ≤ 36 := by linarith
  have := Real.exp_le_exp.mpr this
  linarith

theorem cube_div_six_le_exp (x : ℝ) (hx : 0 ≤ x) : x ^ 3 / 6 ≤ Real.exp x := by
  have h := Real.pow_div_factorial_le_exp x hx 3
  simpa [Nat.factorial] using h

/-! ### The swap -/
theorem exists_swap : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ ∀ N : ℕ, 2 ≤ N → ∀ n : ℕ, Even n → 2 ≤ n →
    ∀ θ : ℝ, |θ| ≤ θ₀ → ∀ M : Mat N, M.IsHermitian →
      Integrable (fun w => Ft θ n (M + gMat w)) (gauss N) ∧
      (∑ τ : Equiv.Perm (Fin N), Ft θ n (M + xMat τ)) / (N.factorial : ℝ) ≤
        Real.exp (K * |θ| ^ 3) * ∫ w, Ft θ n (M + gMat w) ∂gauss N := by
  have hK3 := K3_pos
  refine ⟨2 * K3, min 1 (1 / (2 * K3)), by positivity, lt_min one_pos (by positivity), ?_⟩
  intro N hN n hn hn2 θ hθ M hM
  have hθ0 : 0 ≤ |θ| := abs_nonneg θ
  have hθ1 : |θ| ≤ 1 := hθ.trans (min_le_left _ _)
  have hθ2 : |θ| ≤ 1 / (2 * K3) := hθ.trans (min_le_right _ _)
  have hθ3 : |θ| ^ 3 ≤ |θ| := by
    calc |θ| ^ 3 = |θ| * |θ| ^ 2 := by ring
      _ ≤ |θ| * 1 := by gcongr; exact pow_le_one₀ hθ0 hθ1
      _ = |θ| := mul_one _
  have hFt0 : ∀ M' : Mat N, M'.IsHermitian → 0 ≤ Ft θ n M' := by
    intro M' hM'
    have := Fn_nonneg θ n hn M' hM'
    unfold Ft; positivity
  have hF0 : 0 ≤ Ft θ n M := hFt0 M hM
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  -- integrability
  have hint : Integrable (fun w => Ft θ n (M + gMat w)) (gauss N) := by
    refine Integrable.mono' ((integrable_exp_norm_gMat hN |θ| hθ0).mul_const (Ft θ n M))
      (continuous_Ft_gMat θ n M).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hFt0 _ (hM.add (gMat_isHermitian w)))]
    exact Ft_add_le θ n hn hn2 M (gMat w) hM (gMat_isHermitian w)
  refine ⟨hint, ?_⟩
  set avg := (∑ τ : Equiv.Perm (Fin N), Ft θ n (M + xMat τ)) / (N.factorial : ℝ) with havg
  set I := ∫ w, Ft θ n (M + gMat w) ∂gauss N with hI
  -- the permutation side
  have hperm : ∀ τ : Equiv.Perm (Fin N), Ft θ n (M + xMat τ) ≤
      Ft θ n M + linTerm θ n M (xMat τ) + quadTerm θ n M (xMat τ) +
        |θ| ^ 3 * (64 / 6 * Real.exp 4) * Ft θ n M := by
    intro τ
    have h := abs_Fn_add_sub_le θ n hn hn2 M (xMat τ) hM (xMat_isHermitian τ)
    have hx := norm_xMat_le τ
    have hx0 := norm_nonneg (xMat τ)
    have h3 : ‖xMat τ‖ ^ 3 ≤ 64 := by
      calc ‖xMat τ‖ ^ 3 ≤ 4 ^ 3 := pow_le_pow_left₀ hx0 hx 3
        _ = 64 := by norm_num
    have he : Real.exp (|θ| * ‖xMat τ‖) ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hb : |θ| ^ 3 * ‖xMat τ‖ ^ 3 / 6 * Real.exp (|θ| * ‖xMat τ‖) * Ft θ n M ≤
        |θ| ^ 3 * (64 / 6 * Real.exp 4) * Ft θ n M := by
      refine mul_le_mul_of_nonneg_right ?_ hF0
      calc |θ| ^ 3 * ‖xMat τ‖ ^ 3 / 6 * Real.exp (|θ| * ‖xMat τ‖)
          ≤ |θ| ^ 3 * 64 / 6 * Real.exp 4 := by gcongr
        _ = |θ| ^ 3 * (64 / 6 * Real.exp 4) := by ring
    have := (abs_le.mp (h.trans hb)).2
    unfold Ft at this ⊢
    linarith
  have hA : avg ≤ Ft θ n M + qExpr θ n M + |θ| ^ 3 * (64 / 6 * Real.exp 4) * Ft θ n M := by
    rw [havg, div_le_iff₀ hfact]
    calc ∑ τ : Equiv.Perm (Fin N), Ft θ n (M + xMat τ)
        ≤ ∑ τ : Equiv.Perm (Fin N), (Ft θ n M + linTerm θ n M (xMat τ) +
            quadTerm θ n M (xMat τ) + |θ| ^ 3 * (64 / 6 * Real.exp 4) * Ft θ n M) :=
          Finset.sum_le_sum fun τ _ => hperm τ
      _ = (N.factorial : ℝ) * Ft θ n M + ∑ τ : Equiv.Perm (Fin N), linTerm θ n M (xMat τ) +
            ∑ τ : Equiv.Perm (Fin N), quadTerm θ n M (xMat τ) +
            (N.factorial : ℝ) * (|θ| ^ 3 * (64 / 6 * Real.exp 4) * Ft θ n M) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := by
          rw [sum_linTerm (by omega), sum_quadTerm hN]; ring
  -- the Gaussian side
  have hgauss : ∀ w : Fin N × Fin N → ℝ,
      Ft θ n M + linTerm θ n M (gMat w) + quadTerm θ n M (gMat w) -
        Real.exp (2 * ‖gMat w‖) * (|θ| ^ 3 * Ft θ n M) ≤ Ft θ n (M + gMat w) := by
    intro w
    have h := abs_Fn_add_sub_le θ n hn hn2 M (gMat w) hM (gMat_isHermitian w)
    have hx0 := norm_nonneg (gMat w)
    have h3 := cube_div_six_le_exp ‖gMat w‖ hx0
    have he : Real.exp (|θ| * ‖gMat w‖) ≤ Real.exp ‖gMat w‖ :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he2 : Real.exp (2 * ‖gMat w‖) = Real.exp ‖gMat w‖ * Real.exp ‖gMat w‖ := by
      rw [← Real.exp_add]; ring_nf
    have hb : |θ| ^ 3 * ‖gMat w‖ ^ 3 / 6 * Real.exp (|θ| * ‖gMat w‖) * Ft θ n M ≤
        Real.exp (2 * ‖gMat w‖) * (|θ| ^ 3 * Ft θ n M) := by
      rw [he2]
      calc |θ| ^ 3 * ‖gMat w‖ ^ 3 / 6 * Real.exp (|θ| * ‖gMat w‖) * Ft θ n M
          = (‖gMat w‖ ^ 3 / 6) * Real.exp (|θ| * ‖gMat w‖) * (|θ| ^ 3 * Ft θ n M) := by ring
        _ ≤ Real.exp ‖gMat w‖ * Real.exp ‖gMat w‖ * (|θ| ^ 3 * Ft θ n M) := by gcongr
    have := (abs_le.mp (h.trans hb)).1
    unfold Ft at this ⊢
    linarith
  have hE : Integrable (fun w => Real.exp (2 * ‖gMat w‖)) (gauss N) :=
    integrable_exp_norm_gMat hN 2 (by norm_num)
  have hG : Ft θ n M + qExpr θ n M - 16 * Real.exp 36 * (|θ| ^ 3 * Ft θ n M) ≤ I := by
    have hint2 : Integrable (fun w => Ft θ n M + linTerm θ n M (gMat w) + quadTerm θ n M (gMat w) -
        Real.exp (2 * ‖gMat w‖) * (|θ| ^ 3 * Ft θ n M)) (gauss N) :=
      (((integrable_const _).add (integrable_linTerm θ n M)).add (integrable_quadTerm θ n M)).sub
        (hE.mul_const _)
    have hmono := integral_mono hint2 hint hgauss
    have i1 : Integrable (fun _ : Fin N × Fin N → ℝ => Ft θ n M) (gauss N) := integrable_const _
    have i2 : Integrable (fun w => Ft θ n M + linTerm θ n M (gMat w)) (gauss N) :=
      i1.add (integrable_linTerm θ n M)
    have i3 : Integrable (fun w => Ft θ n M + linTerm θ n M (gMat w) + quadTerm θ n M (gMat w))
        (gauss N) := i2.add (integrable_quadTerm θ n M)
    have i4 : Integrable (fun w => Real.exp (2 * ‖gMat w‖) * (|θ| ^ 3 * Ft θ n M)) (gauss N) :=
      hE.mul_const _
    rw [integral_sub i3 i4, integral_add i2 (integrable_quadTerm θ n M),
      integral_add i1 (integrable_linTerm θ n M),
      integral_linTerm, integral_quadTerm hN, integral_mul_const, integral_const] at hmono
    simp only [probReal_univ, smul_eq_mul, one_mul, add_zero] at hmono
    have h16 := integral_exp_two_le hN
    have : (∫ w, Real.exp (2 * ‖gMat w‖) ∂gauss N) * (|θ| ^ 3 * Ft θ n M) ≤
        16 * Real.exp 36 * (|θ| ^ 3 * Ft θ n M) := by gcongr
    linarith
  -- comparing `Ft θ n M` with the average
  have hB : Ft θ n M ≤ Real.exp 4 * avg := by
    have hτ : ∀ τ : Equiv.Perm (Fin N), Ft θ n M ≤ Real.exp 4 * Ft θ n (M + xMat τ) := by
      intro τ
      have hH := hM.add (xMat_isHermitian τ)
      have hneg : (-xMat τ).IsHermitian := (xMat_isHermitian τ).neg
      have h := Ft_add_le θ n hn hn2 (M + xMat τ) (-xMat τ) hH hneg
      rw [add_neg_cancel_right, norm_neg] at h
      refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hFt0 _ hH))
      nlinarith [norm_xMat_le τ, norm_nonneg (xMat τ)]
    have h1 : ∑ _τ : Equiv.Perm (Fin N), Ft θ n M = (N.factorial : ℝ) * Ft θ n M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]
    have h2 : ∑ _τ : Equiv.Perm (Fin N), Ft θ n M ≤
        ∑ τ : Equiv.Perm (Fin N), Real.exp 4 * Ft θ n (M + xMat τ) :=
      Finset.sum_le_sum fun τ _ => hτ τ
    rw [h1, ← Finset.mul_sum] at h2
    have h3 : Real.exp 4 * avg =
        Real.exp 4 * (∑ τ : Equiv.Perm (Fin N), Ft θ n (M + xMat τ)) / (N.factorial : ℝ) := by
      rw [havg]; ring
    rw [h3, le_div_iff₀ hfact]
    linarith
  have havg0 : 0 ≤ avg := by
    rw [havg]
    exact div_nonneg (Finset.sum_nonneg fun τ _ => hFt0 _ (hM.add (xMat_isHermitian τ))) hfact.le
  -- conclusion
  set u := K3 * |θ| ^ 3 with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 2 := by
    calc u ≤ K3 * |θ| := by rw [hu]; gcongr
      _ ≤ K3 * (1 / (2 * K3)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hdiff : avg - I ≤ u * avg := by
    have h1 : avg - I ≤ |θ| ^ 3 * (64 / 6 * Real.exp 4 + 16 * Real.exp 36) * Ft θ n M := by
      linarith
    have h2 : |θ| ^ 3 * (64 / 6 * Real.exp 4 + 16 * Real.exp 36) * Ft θ n M ≤
        |θ| ^ 3 * (64 / 6 * Real.exp 4 + 16 * Real.exp 36) * (Real.exp 4 * avg) := by gcongr
    calc avg - I ≤ |θ| ^ 3 * (64 / 6 * Real.exp 4 + 16 * Real.exp 36) * (Real.exp 4 * avg) :=
          h1.trans h2
      _ = u * avg := by rw [hu]; unfold K3; ring
  have hexp : Real.exp (-(2 * u)) ≤ 1 - u := by
    have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
    rw [Real.exp_neg]
    have hpos : (0 : ℝ) < 1 + 2 * u := by linarith
    calc (Real.exp (2 * u))⁻¹ ≤ (1 + 2 * u)⁻¹ := inv_anti₀ hpos h1
      _ ≤ 1 - u := by
          rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
  have hfin : avg * Real.exp (-(2 * u)) ≤ I := by
    calc avg * Real.exp (-(2 * u)) ≤ avg * (1 - u) := mul_le_mul_of_nonneg_left hexp havg0
      _ ≤ I := by linarith
  have hKu : 2 * K3 * |θ| ^ 3 = 2 * u := by rw [hu]; ring
  rw [hKu]
  calc avg = Real.exp (2 * u) * (avg * Real.exp (-(2 * u))) := by
        rw [mul_comm avg, ← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (2 * u) * I := by gcongr

end StrongConv.T38.PartS
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part S: one Lindeberg swap -/
alias exists_swap := StrongConv.T38.PartS.exists_swap

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartF
/-- Integrability of the test function along the Gaussian model, at any symmetric base point. -/
theorem integrable_Ft_gSum {N : ℕ} (hN : 2 ≤ N) (d : ℕ) (θ : ℝ) (n : ℕ) (hn : Even n)
    (hn1 : 1 ≤ n) (M : Mat N) (hM : M.IsHermitian) :
    Integrable (fun w => Ft θ n (M + gSum w)) (gaussPow d N) := by
  have hcont : Continuous (fun w : Fin d → Fin N × Fin N → ℝ => Ft θ n (M + gSum w)) :=
    (continuous_Ft θ n).comp (continuous_const.add continuous_gSum)
  have hbound : Integrable (fun w : Fin d → Fin N × Fin N → ℝ =>
      (N : ℝ) * Real.exp (|θ| * ‖M‖) * Real.exp (|θ| * ‖gSum w‖) + N) (gaussPow d N) :=
    ((StrongConv.T38.integrable_exp_norm_gSum hN d |θ| (abs_nonneg θ)).const_mul _).add
      (integrable_const _)
  refine hbound.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have hH : (M + gSum w).IsHermitian := hM.add (gSum_isHermitian w)
  have h0 := StrongConv.T38.Fn_nonneg θ n hn (M + gSum w) hH
  have h1 := StrongConv.T38.Fn_le_exp θ n hn1 (M + gSum w) hH
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h2 : Real.exp (|θ| * ‖M + gSum w‖) ≤ Real.exp (|θ| * ‖M‖) * Real.exp (|θ| * ‖gSum w‖) := by
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg θ))
  have h3 := mul_le_mul_of_nonneg_left h2 hN0
  unfold Ft
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith

theorem xSum_cons {d N : ℕ} (τ : Equiv.Perm (Fin N)) (σ : Fin d → Equiv.Perm (Fin N)) :
    xSum (Fin.cons τ σ : Fin (d + 1) → Equiv.Perm (Fin N)) = xMat τ + xSum σ := by
  simp [xSum, Fin.sum_univ_succ]

theorem gSum_insertNth {d N : ℕ} (x : Fin N × Fin N → ℝ) (w : Fin d → Fin N × Fin N → ℝ) :
    gSum ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Fin N × Fin N → ℝ) 0).symm
      (x, w)) = gMat x + gSum w := by
  simp [gSum, Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem chain_aux (K θ₀ : ℝ)
    (hS : ∀ N : ℕ, 2 ≤ N → ∀ n : ℕ, Even n → 2 ≤ n →
      ∀ θ : ℝ, |θ| ≤ θ₀ → ∀ M : Mat N, M.IsHermitian →
        Integrable (fun w => Ft θ n (M + gMat w)) (gauss N) ∧
        (∑ τ : Equiv.Perm (Fin N), Ft θ n (M + xMat τ)) / (N.factorial : ℝ) ≤
          Real.exp (K * |θ| ^ 3) * ∫ w, Ft θ n (M + gMat w) ∂gauss N)
    (N : ℕ) (hN : 2 ≤ N) (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (θ : ℝ) (hθ : |θ| ≤ θ₀) :
    ∀ d : ℕ, ∀ M : Mat N, M.IsHermitian →
      (∑ σ : Fin d → Equiv.Perm (Fin N), Ft θ n (M + xSum σ)) / ((N.factorial : ℝ) ^ d) ≤
        Real.exp (K * d * |θ| ^ 3) * ∫ w, Ft θ n (M + gSum w) ∂gaussPow d N := by
  have hn1 : 1 ≤ n := by omega
  have hc : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  intro d
  induction d with
  | zero =>
    intro M hM
    simp [xSum, gSum]
  | succ d ih =>
    intro M hM
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Fin N × Fin N → ℝ) 0
    have mp : MeasurePreserving e (gaussPow (d + 1) N) ((gauss N).prod (gaussPow d N)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => gauss N) 0
    have hint := integrable_Ft_gSum hN (d + 1) θ n hn hn1 M hM
    have hprod : Integrable (fun p : (Fin N × Fin N → ℝ) × (Fin d → Fin N × Fin N → ℝ) =>
        Ft θ n ((M + gSum p.2) + gMat p.1)) ((gauss N).prod (gaussPow d N)) := by
      have := (mp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hint
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp_apply]
      rw [show p = (p.1, p.2) from rfl, gSum_insertNth, add_assoc, add_comm (gSum p.2)]
    have hsum : ∑ σ : Fin (d + 1) → Equiv.Perm (Fin N), Ft θ n (M + xSum σ) =
        ∑ τ : Equiv.Perm (Fin N), ∑ σ' : Fin d → Equiv.Perm (Fin N),
          Ft θ n ((M + xMat τ) + xSum σ') := by
      rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => Equiv.Perm (Fin N))).sum_comp,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ' _ => ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk]
      rw [xSum_cons, add_assoc]
    have hE : (0 : ℝ) ≤ Real.exp (K * d * |θ| ^ 3) := (Real.exp_pos _).le
    have hi : ∀ τ : Equiv.Perm (Fin N),
        Integrable (fun w => Ft θ n ((M + xMat τ) + gSum w)) (gaussPow d N) := fun τ =>
      integrable_Ft_gSum hN d θ n hn hn1 _ (hM.add (xMat_isHermitian τ))
    calc (∑ σ : Fin (d + 1) → Equiv.Perm (Fin N), Ft θ n (M + xSum σ)) /
          ((N.factorial : ℝ) ^ (d + 1))
        = (∑ τ : Equiv.Perm (Fin N), (∑ σ' : Fin d → Equiv.Perm (Fin N),
            Ft θ n ((M + xMat τ) + xSum σ')) / ((N.factorial : ℝ) ^ d)) / (N.factorial : ℝ) := by
          rw [hsum, ← Finset.sum_div, div_div, pow_succ]
      _ ≤ (∑ τ : Equiv.Perm (Fin N), Real.exp (K * d * |θ| ^ 3) *
            ∫ w, Ft θ n ((M + xMat τ) + gSum w) ∂gaussPow d N) / (N.factorial : ℝ) := by
          gcongr with τ _
          exact ih _ (hM.add (xMat_isHermitian τ))
      _ = Real.exp (K * d * |θ| ^ 3) * ∫ w, (∑ τ : Equiv.Perm (Fin N),
            Ft θ n ((M + gSum w) + xMat τ)) / (N.factorial : ℝ) ∂gaussPow d N := by
          rw [← Finset.mul_sum, ← integral_finsetSum _ (fun τ _ => hi τ), mul_div_assoc,
            ← integral_div]
          simp only [add_right_comm]
      _ ≤ Real.exp (K * d * |θ| ^ 3) * ∫ w, Real.exp (K * |θ| ^ 3) *
            ∫ x, Ft θ n ((M + gSum w) + gMat x) ∂gauss N ∂gaussPow d N := by
          refine mul_le_mul_of_nonneg_left ?_ hE
          refine integral_mono ?_ ?_ fun w =>
            (hS N hN n hn hn2 θ hθ (M + gSum w) (hM.add (gSum_isHermitian w))).2
          · refine Integrable.div_const ?_ _
            refine integrable_finsetSum _ fun τ _ => ?_
            simpa only [add_right_comm] using hi τ
          · exact (hprod.integral_prod_right).const_mul _
      _ = Real.exp (K * (d + 1 : ℕ) * |θ| ^ 3) * ∫ w, Ft θ n (M + gSum w) ∂gaussPow (d + 1) N := by
          rw [integral_const_mul, ← integral_prod_symm _ hprod, ← mul_assoc, ← Real.exp_add,
            ← mp.symm.integral_comp' (g := fun w => Ft θ n (M + gSum w))]
          congr 1
          · push_cast; ring_nf
          · refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            simp only
            rw [show p = (p.1, p.2) from rfl, gSum_insertNth, add_assoc, add_comm (gSum p.2)]

theorem exists_chain : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ ∀ N : ℕ, 2 ≤ N → ∀ d n : ℕ, Even n → 2 ≤ n →
    ∀ θ : ℝ, |θ| ≤ θ₀ →
      Integrable (fun w => Ft θ n (gSum w)) (gaussPow d N) ∧
      (∑ σ : Fin d → Equiv.Perm (Fin N), Ft θ n (xSum σ)) /
          (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≤
        Real.exp (K * d * |θ| ^ 3) * ∫ w, Ft θ n (gSum w) ∂gaussPow d N := by
  obtain ⟨K, θ₀, hK, hθ₀, hS⟩ := StrongConv.T38.exists_swap
  refine ⟨K, θ₀, hK, hθ₀, fun N hN d n hn hn2 θ hθ => ?_⟩
  have h0 : (0 : Mat N).IsHermitian := Matrix.isHermitian_zero
  constructor
  · simpa using integrable_Ft_gSum hN d θ n hn (by omega) 0 h0
  · have h := chain_aux K θ₀ hS N hN n hn hn2 θ hθ d 0 h0
    have hcard : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) = (N.factorial : ℝ) ^ d := by
      simp [Fintype.card_perm]
    rw [hcard]
    simpa using h

end StrongConv.T38.PartF
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part F: the chain of `d` swaps -/
alias exists_chain := StrongConv.T38.PartF.exists_chain

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.PartG
open StrongConv.T38
theorem integral_Ft_gSum_le {N : ℕ} (hN : 2 ≤ N) (d n : ℕ) (hn1 : 1 ≤ n) (θ' : ℝ)
    (hint : Integrable (fun w => Ft θ' n (gSum w)) (gaussPow d N)) :
    ∫ w, Ft θ' n (gSum w) ∂gaussPow d N ≤ N * (1 + 16 * Real.exp (bexp N d |θ'|)) := by
  have hI := StrongConv.T38.integrable_exp_norm_gSum hN d |θ'| (abs_nonneg _)
  have hle := StrongConv.T38.integral_exp_norm_gSum_le hN d |θ'| (abs_nonneg _)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc ∫ w, Ft θ' n (gSum w) ∂gaussPow d N
      ≤ ∫ w, ((N : ℝ) + N * Real.exp (|θ'| * ‖gSum w‖)) ∂gaussPow d N := by
        apply integral_mono hint ((integrable_const _).add (hI.const_mul _))
        intro w
        show Ft θ' n (gSum w) ≤ (N : ℝ) + N * Real.exp (|θ'| * ‖gSum w‖)
        have := StrongConv.T38.Fn_le_exp θ' n hn1 (gSum w) (gSum_isHermitian w)
        simp only [Ft]
        linarith
    _ = N + N * ∫ w, Real.exp (|θ'| * ‖gSum w‖) ∂gaussPow d N := by
        rw [integral_add (integrable_const _) (hI.const_mul _), integral_const_mul]
        simp
    _ ≤ N * (1 + 16 * Real.exp (bexp N d |θ'|)) := by
        have := mul_le_mul_of_nonneg_left hle hN0
        unfold bexp
        linarith

theorem markov_step {N : ℕ} (hN : 2 ≤ N) (d n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (θ L K : ℝ)
    (hθ : 0 ≤ θ) (hL : 0 ≤ L)
    (hc1 : Integrable (fun w => Ft θ n (gSum w)) (gaussPow d N) ∧
      (∑ σ : Fin d → Equiv.Perm (Fin N), Ft θ n (xSum σ)) /
          (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≤
        Real.exp (K * d * |θ| ^ 3) * ∫ w, Ft θ n (gSum w) ∂gaussPow d N)
    (hc2 : Integrable (fun w => Ft (-θ) n (gSum w)) (gaussPow d N) ∧
      (∑ σ : Fin d → Equiv.Perm (Fin N), Ft (-θ) n (xSum σ)) /
          (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≤
        Real.exp (K * d * |(-θ)| ^ 3) * ∫ w, Ft (-θ) n (gSum w) ∂gaussPow d N) :
    ((Finset.univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => L < ‖xSum σ‖).card : ℝ) /
        (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) * (1 + θ * L / n) ^ n ≤
      34 * N * Real.exp (K * d * θ ^ 3 + bexp N d θ) := by
  have hn1 : 1 ≤ n := by omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set c : ℝ := (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) with hc
  have hcpos : 0 < c := by
    rw [hc]; exact_mod_cast Fintype.card_pos
  set S := Finset.univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => L < ‖xSum σ‖ with hS
  set A : ℝ := (1 + θ * L / n) ^ n with hA
  have h1 : (S.card : ℝ) * A ≤ ∑ σ : Fin d → Equiv.Perm (Fin N),
      (Fn θ n (xSum σ) + Fn (-θ) n (xSum σ)) := by
    calc (S.card : ℝ) * A = ∑ _σ ∈ S, A := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ σ ∈ S, (Fn θ n (xSum σ) + Fn (-θ) n (xSum σ)) := by
          apply Finset.sum_le_sum
          intro σ hσ
          have hσ' : L < ‖xSum σ‖ := (Finset.mem_filter.mp hσ).2
          have hp := StrongConv.T38.pow_le_Fn_add_Fn_neg hN1 θ hθ n hn hn1 (xSum σ)
            (xSum_isHermitian σ)
          refine le_trans ?_ hp
          apply pow_le_pow_left₀ (by positivity)
          have : θ * L / n ≤ θ * ‖xSum σ‖ / n := by
            apply div_le_div_of_nonneg_right _ hn0.le
            exact mul_le_mul_of_nonneg_left hσ'.le hθ
          linarith
      _ ≤ ∑ σ : Fin d → Equiv.Perm (Fin N), (Fn θ n (xSum σ) + Fn (-θ) n (xSum σ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro σ _ _
          exact add_nonneg (StrongConv.T38.Fn_nonneg θ n hn _ (xSum_isHermitian σ))
            (StrongConv.T38.Fn_nonneg (-θ) n hn _ (xSum_isHermitian σ))
  have h2 : ∑ σ : Fin d → Equiv.Perm (Fin N), (Fn θ n (xSum σ) + Fn (-θ) n (xSum σ)) ≤
      (∑ σ : Fin d → Equiv.Perm (Fin N), Ft θ n (xSum σ)) +
        ∑ σ : Fin d → Equiv.Perm (Fin N), Ft (-θ) n (xSum σ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro σ _
    simp only [Ft]
    linarith
  have hi1 := integral_Ft_gSum_le hN d n hn1 θ hc1.1
  have hi2 := integral_Ft_gSum_le hN d n hn1 (-θ) hc2.1
  have e1 := hc1.2
  have e2 := hc2.2
  rw [abs_neg] at e2 hi2
  rw [abs_of_nonneg hθ] at e1 e2 hi1 hi2
  set Eθ := Real.exp (K * d * θ ^ 3) with hEθ
  have hEpos : 0 < Eθ := Real.exp_pos _
  have hb1 : (1 : ℝ) ≤ Real.exp (bexp N d θ) := Real.one_le_exp (bexp_nonneg hN d θ hθ)
  have e1' := e1.trans (mul_le_mul_of_nonneg_left hi1 hEpos.le)
  have e2' := e2.trans (mul_le_mul_of_nonneg_left hi2 hEpos.le)
  have h3 : (S.card : ℝ) / c * A = ((S.card : ℝ) * A) / c := by ring
  rw [h3, Real.exp_add, ← hEθ]
  have h4 : ((S.card : ℝ) * A) / c ≤
      (∑ σ : Fin d → Equiv.Perm (Fin N), Ft θ n (xSum σ)) / c +
        (∑ σ : Fin d → Equiv.Perm (Fin N), Ft (-θ) n (xSum σ)) / c := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (h1.trans h2) hcpos.le
  have h5 : Eθ * ((N : ℝ) * (1 + 16 * Real.exp (bexp N d θ))) ≤
      17 * N * (Eθ * Real.exp (bexp N d θ)) := by
    have : (N : ℝ) * (1 + 16 * Real.exp (bexp N d θ)) ≤ N * (17 * Real.exp (bexp N d θ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hN0
    have := mul_le_mul_of_nonneg_left this hEpos.le
    linarith
  linarith

theorem exponent_bound (K θ₀ C₀ t s sg D η θ : ℝ) (hK : 0 < K) (hθ₀ : 0 < θ₀)
    (hC : C₀ = 1 / θ₀ + 48 + 16 * K) (ht : 1 ≤ t) (hs : 0 ≤ s) (hsg : 0 ≤ sg) (hD : 0 ≤ D)
    (hDsg : 2 * D ≤ sg ^ 2)
    (hη : η = C₀ * (s * Real.sqrt t + (4 : ℝ) ^ ((1 : ℝ) / 3) * sg ^ ((2 : ℝ) / 3) *
      t ^ ((2 : ℝ) / 3) + 4 * t))
    (hθ : θ = 4 * t / η) :
    0 ≤ η ∧ 0 ≤ θ ∧ θ ≤ θ₀ ∧ θ * η = 4 * t ∧
      K * D * θ ^ 3 + 3 * (θ * s) + θ ^ 2 * s ^ 2 ≤ t := by
  have hinv : 0 < 1 / θ₀ := by positivity
  have hC48 : 48 ≤ C₀ := by rw [hC]; linarith
  have hCK : 16 * K ≤ C₀ := by rw [hC]; linarith
  have hCθ : 1 / θ₀ ≤ C₀ := by rw [hC]; linarith
  have hC0 : 0 < C₀ := by linarith
  have ht0 : 0 < t := by linarith
  set q := Real.sqrt t with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr ht0
  have hqq : q * q = t := Real.mul_self_sqrt ht0.le
  have hqt : q ≤ t := by nlinarith
  set r := (4 : ℝ) ^ ((1 : ℝ) / 3) * sg ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr3 : r ^ 3 = 4 * sg ^ 2 * t ^ 2 := by
    have e1 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have e2 : (sg ^ ((2 : ℝ) / 3)) ^ 3 = sg ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hsg]; norm_num
    have e3 : (t ^ ((2 : ℝ) / 3)) ^ 3 = t ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    rw [hr, mul_pow, mul_pow, e1, e2, e3]
  have hη' : η = C₀ * (s * q + r + 4 * t) := hη
  have hsq0 : 0 ≤ s * q := by positivity
  have hη4 : C₀ * (4 * t) ≤ η := by
    rw [hη']; exact mul_le_mul_of_nonneg_left (by linarith) hC0.le
  have hηs : C₀ * (s * q) ≤ η := by
    rw [hη']; exact mul_le_mul_of_nonneg_left (by linarith) hC0.le
  have hηr : C₀ * r ≤ η := by
    rw [hη']; exact mul_le_mul_of_nonneg_left (by linarith) hC0.le
  have hηpos : 0 < η := lt_of_lt_of_le (by positivity) hη4
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθη : θ * η = 4 * t := by rw [hθ]; field_simp
  have hθC : θ * C₀ ≤ 1 := by
    have : θ * (C₀ * (4 * t)) ≤ 4 * t :=
      (mul_le_mul_of_nonneg_left hη4 hθ0).trans hθη.le
    have h4t : 0 < 4 * t := by linarith
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  have hθle : θ ≤ θ₀ := by
    have h1 : θ * (1 / θ₀) ≤ 1 := (mul_le_mul_of_nonneg_left hCθ hθ0).trans hθC
    rw [mul_one_div, div_le_one hθ₀] at h1
    exact h1
  refine ⟨hηpos.le, hθ0, hθle, hθη, ?_⟩
  -- the `s` terms
  set u := θ * s with hu
  have hu0 : 0 ≤ u := by positivity
  have huC : C₀ * u ≤ 4 * q := by
    have h1 : θ * (C₀ * (s * q)) ≤ 4 * (q * q) := by
      rw [hqq, ← hθη]; exact mul_le_mul_of_nonneg_left hηs hθ0
    have h2 : (C₀ * u) * q ≤ (4 * q) * q := by
      rw [hu]; linarith
    exact le_of_mul_le_mul_right h2 hq0
  have hu48 : 48 * u ≤ 4 * q := (mul_le_mul_of_nonneg_right hC48 hu0).trans huC
  have hu1 : 3 * u ≤ t / 4 := by linarith
  have hu2 : u ^ 2 ≤ t / 4 := by
    have : (48 * u) ^ 2 ≤ (4 * q) ^ 2 := pow_le_pow_left₀ (by positivity) hu48 2
    nlinarith
  -- the cubic term
  have hcub : (θ * (C₀ * r)) ^ 3 ≤ (4 * t) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [← hθη]; exact mul_le_mul_of_nonneg_left hηr hθ0
  have hcub2 : θ ^ 3 * C₀ ^ 3 * sg ^ 2 ≤ 16 * t := by
    have h1 : (θ ^ 3 * C₀ ^ 3 * sg ^ 2) * (4 * t ^ 2) ≤ (16 * t) * (4 * t ^ 2) := by
      have : (θ * (C₀ * r)) ^ 3 = (θ ^ 3 * C₀ ^ 3 * sg ^ 2) * (4 * t ^ 2) := by
        rw [mul_pow, mul_pow, hr3]; ring
      rw [← this]
      calc (θ * (C₀ * r)) ^ 3 ≤ (4 * t) ^ 3 := hcub
        _ = (16 * t) * (4 * t ^ 2) := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hθC3 : 0 ≤ θ ^ 3 * C₀ ^ 3 := by positivity
  have hcub3 : θ ^ 3 * C₀ ^ 3 * (2 * D) ≤ 16 * t :=
    (mul_le_mul_of_nonneg_left hDsg hθC3).trans hcub2
  have hC1 : C₀ ≤ C₀ ^ 3 := by
    have : 1 ≤ C₀ := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C₀ - 1) (by linarith : (0 : ℝ) ≤ C₀),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C₀ - 1) (by linarith : (0 : ℝ) ≤ C₀))
        (by linarith : (0 : ℝ) ≤ C₀)]
  have hKD : K * D * θ ^ 3 ≤ t / 2 := by
    have h1 : C₀ ^ 3 * (K * D * θ ^ 3) ≤ 8 * K * t := by
      have := mul_le_mul_of_nonneg_left hcub3 hK.le
      nlinarith
    have h2 : 8 * K * t ≤ C₀ ^ 3 * (t / 2) := by
      have h3 : 16 * K * t ≤ C₀ * t := mul_le_mul_of_nonneg_right hCK ht0.le
      have h4 : C₀ * t ≤ C₀ ^ 3 * t := mul_le_mul_of_nonneg_right hC1 ht0.le
      linarith
    exact le_of_mul_le_mul_left (h1.trans h2) (by positivity)
  have : θ ^ 2 * s ^ 2 = u ^ 2 := by rw [hu]; ring
  rw [this]
  linarith

theorem exists_tail : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ N d : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
    ((Finset.univ.filter fun σ : Fin d → Equiv.Perm (Fin N) =>
        2 * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) +
          C₀ * (Real.sqrt (4 * d / ((N : ℝ) - 1)) * Real.sqrt t +
            (4 : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt (2 * d * N / ((N : ℝ) - 1)) ^ ((2 : ℝ) / 3) *
              t ^ ((2 : ℝ) / 3) + 4 * t) < ‖xSum σ‖).card : ℝ) /
        (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≤ 4 * N * Real.exp (-t) := by
  obtain ⟨K, θ₀, hK, hθ₀, hchain⟩ := StrongConv.T38.exists_chain
  refine ⟨1 / θ₀ + 48 + 16 * K, by positivity, ?_⟩
  intro N d hN t ht
  set C₀ : ℝ := 1 / θ₀ + 48 + 16 * K with hC
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hcpos : (0 : ℝ) < (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  set sg := Real.sqrt (2 * d * N / ((N : ℝ) - 1)) with hsg
  set s := Real.sqrt (4 * d / ((N : ℝ) - 1)) with hs
  set η := C₀ * (s * Real.sqrt t + (4 : ℝ) ^ ((1 : ℝ) / 3) * sg ^ ((2 : ℝ) / 3) *
      t ^ ((2 : ℝ) / 3) + 4 * t) with hη
  set S := Finset.univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => 2 * sg + η < ‖xSum σ‖
    with hS
  set P : ℝ := (S.card : ℝ) / (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) with hP
  have hP0 : 0 ≤ P := by positivity
  have hP1 : P ≤ 1 := by
    rw [hP, div_le_one hcpos]
    have : S.card ≤ Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.filter_subset _ _)
    exact_mod_cast this
  by_cases htriv : 1 ≤ 4 * N * Real.exp (-t)
  · exact hP1.trans htriv
  rw [not_le] at htriv
  set x := Real.exp (-t) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx8 : x < 1 / 8 := by nlinarith
  have ht1 : 1 ≤ t := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : Real.exp (-1) < x := Real.exp_lt_exp.mpr (by linarith)
    have h2 := Real.exp_neg_one_gt_d9
    linarith
  set θ := 4 * t / η with hθ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsg2 : sg ^ 2 = 2 * d * N / ((N : ℝ) - 1) := Real.sq_sqrt (by positivity)
  have hs2 : s ^ 2 = 4 * d / ((N : ℝ) - 1) := Real.sq_sqrt (by positivity)
  have hDsg : 2 * (d : ℝ) ≤ sg ^ 2 := by
    rw [hsg2, le_div_iff₀ hN1]
    nlinarith
  obtain ⟨hη0, hθ0, hθle, hθη, hexp⟩ := exponent_bound K θ₀ C₀ t s sg d η θ hK hθ₀ hC ht1
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hd0 hDsg hη hθ
  have hΛ0 : 0 ≤ 2 * sg + η := by
    have : 0 ≤ sg := Real.sqrt_nonneg _
    linarith
  -- the bound for every even `n`
  have hstep : ∀ m : ℕ, P * (1 + θ * (2 * sg + η) / ((2 * m + 2 : ℕ) : ℝ)) ^ (2 * m + 2) ≤
      34 * N * Real.exp (K * d * θ ^ 3 + bexp N d θ) := by
    intro m
    have hev : Even (2 * m + 2) := ⟨m + 1, by ring⟩
    have hc1 := hchain N hN d (2 * m + 2) hev (by omega) θ (by rw [abs_of_nonneg hθ0]; exact hθle)
    have hc2 := hchain N hN d (2 * m + 2) hev (by omega) (-θ)
      (by rw [abs_neg, abs_of_nonneg hθ0]; exact hθle)
    exact markov_step hN d (2 * m + 2) hev (by omega) θ (2 * sg + η) K hθ0 hΛ0 hc1 hc2
  have hlim : Filter.Tendsto
      (fun m : ℕ => P * (1 + θ * (2 * sg + η) / ((2 * m + 2 : ℕ) : ℝ)) ^ (2 * m + 2))
      Filter.atTop (nhds (P * Real.exp (θ * (2 * sg + η)))) := by
    apply Filter.Tendsto.const_mul
    have h1 := Real.tendsto_one_add_div_pow_exp (θ * (2 * sg + η))
    have h2 : Filter.Tendsto (fun m : ℕ => 2 * m + 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun m => by simp only [id]; omega) Filter.tendsto_id
    exact h1.comp h2
  have hmain : P * Real.exp (θ * (2 * sg + η)) ≤
      34 * N * Real.exp (K * d * θ ^ 3 + bexp N d θ) := le_of_tendsto' hlim hstep
  -- rewrite the Gaussian exponent
  have hs' : Real.sqrt ((d : ℝ) / ((N : ℝ) - 1)) = s / 2 := by
    have : (4 : ℝ) * d / ((N : ℝ) - 1) = 2 ^ 2 * (d / ((N : ℝ) - 1)) := by ring
    rw [hs, this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  have hb : bexp N d θ = θ * (2 * sg) + 3 * (θ * s) + θ ^ 2 * s ^ 2 := by
    unfold bexp
    rw [hs', hs2, ← hsg]
    ring
  have hfin : P ≤ 34 * N * Real.exp (-(3 * t)) := by
    have hpos : 0 < Real.exp (θ * (2 * sg + η)) := Real.exp_pos _
    have h1 : 34 * (N : ℝ) * Real.exp (K * d * θ ^ 3 + bexp N d θ) ≤
        34 * N * Real.exp (-(3 * t)) * Real.exp (θ * (2 * sg + η)) := by
      rw [mul_assoc (34 * (N : ℝ)), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      rw [hb]
      have : θ * (2 * sg + η) = θ * (2 * sg) + 4 * t := by rw [mul_add, hθη]
      rw [this]
      linarith
    exact le_of_mul_le_mul_right (hmain.trans h1) hpos
  have hx3 : Real.exp (-(3 * t)) = x * x * x := by
    rw [hx, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hx3] at hfin
  have hN0 : (0 : ℝ) < N := by linarith
  have hxx : 34 * (x * x * x) ≤ 4 * x := by nlinarith [mul_pos hx0 hx0]
  have := mul_le_mul_of_nonneg_left hxx hN0.le
  linarith

end StrongConv.T38.PartG
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38
/-! ## Part G: the tail bound for `‖Y‖` -/
alias exists_tail := StrongConv.T38.PartG.exists_tail

end StrongConv.T38
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix ComplexConjugate Filter
open scoped InnerProductSpace
open scoped Matrix.Norms.L2Operator
namespace StrongConv.T38.Up
/-!
# T38 splice: Brailovskaya–van Handel Theorem 3.8 for random regular graphs from `exists_tail`

The assembly of the published reduction (`Y(σ) = ∑ᵢ (Π_{σ i} + Π_{σ i}ᵀ − (2/N)J)` has the norm of
`Aᴺ`; take `t = (a + 1) log N + log 4`), with its one use of Brailovskaya–van Handel Corollary 2.17
replaced by the direct tail bound `StrongConv.T38.exists_tail` for the real matrix `xSum σ`, whose
complexification is `Y(σ)`. The parameters are `σ = √(2dN/(N − 1))`, `s = √(4d/(N − 1))`, `v = 0`,
`R = 4`.
-/
/-- The permutation matrix of `τ`: column `b` is `e_{τ b}` (as `permOp`). -/
def permMat {N : ℕ} (τ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => if τ b = a then 1 else 0

/-- The centred summand `Π_τ + Π_τᵀ − (2/N)J`. -/
def zMat {N : ℕ} (τ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  permMat τ + (permMat τ)ᴴ - ((2 : ℂ) / N) • Matrix.of (fun _ _ => (1 : ℂ))

/-- The random matrix `Y(σ) = ∑ᵢ zMat (σ i)`. -/
def yMat {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ i, zMat (σ i)

/-! ### Coordinates -/
lemma permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

lemma permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

lemma permOpPerp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    (permOpPerp π x : EuclideanSpace ℂ (Fin N)) = permOp π x := rfl

lemma inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪permOp π x, y⟫_ℂ = ⟪x, permOp π⁻¹ y⟫_ℂ := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

lemma star_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    star (permOpPerp π) = permOpPerp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, permOpPerp_apply]
  rw [inner_permOp, inv_inv]

lemma zMat_entry {N : ℕ} (τ : Equiv.Perm (Fin N)) (a b : Fin N) :
    zMat τ a b = (if τ b = a then 1 else 0) + (if τ a = b then 1 else 0) - 2 / N := by
  simp only [zMat, permMat, Matrix.sub_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  congr 2
  split_ifs <;> simp

lemma zMat_mulVec {N : ℕ} (τ : Equiv.Perm (Fin N)) (x : Fin N → ℂ) (a : Fin N) :
    (zMat τ *ᵥ x) a = x (τ.symm a) + x (τ a) - (2 / N) * ∑ b, x b := by
  simp only [Matrix.mulVec, dotProduct, zMat_entry, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.mul_sum]
  congr 2
  · rw [Finset.sum_eq_single (τ.symm a)]
    · simp
    · intro b _ hb; rw [if_neg]
      intro h; exact hb (by rw [← h]; simp)
    · simp
  · rw [Finset.sum_ite_eq]; simp

lemma toE_zMat_apply {N : ℕ} (τ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (a : Fin N) :
    toEuclideanCLM (𝕜 := ℂ) (zMat τ) x a = x (τ.symm a) + x (τ a) - (2 / N) * ∑ b, x b := by
  have := zMat_mulVec τ (WithLp.ofLp x) a
  simpa using this

lemma toE_yMat_apply {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N))
    (a : Fin N) :
    toEuclideanCLM (𝕜 := ℂ) (yMat σ) x a =
      ∑ i, (x ((σ i).symm a) + x (σ i a) - (2 / N) * ∑ b, x b) := by
  simp only [yMat, map_sum, _root_.sum_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [toE_zMat_apply]

lemma mem_onesPerp_iff {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) :
    x ∈ OnesPerp N ↔ ∑ b, x b = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [onesVec, PiLp.inner_apply]

lemma adjPerp_coe_apply {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : OnesPerp N) (a : Fin N) :
    (adjPerp σ x : EuclideanSpace ℂ (Fin N)) a = ∑ i, ((x : EuclideanSpace ℂ (Fin N)) ((σ i).symm a) +
      (x : EuclideanSpace ℂ (Fin N)) (σ i a)) := by
  simp only [adjPerp, sModel, star_permOpPerp, _root_.sum_apply,
    _root_.add_apply, Submodule.coe_sum, Submodule.coe_add, permOpPerp_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [permOp_apply, Equiv.Perm.inv_def]

/-! ### Part Q -/
lemma toE_yMat_onesVec {d N : ℕ} (hN : 1 ≤ N) (σ : Fin d → Equiv.Perm (Fin N)) :
    toEuclideanCLM (𝕜 := ℂ) (yMat σ) (onesVec N) = 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  ext a
  rw [toE_yMat_apply]
  simp only [onesVec, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [div_mul_cancel₀ _ hN']
  simp only [WithLp.ofLp_zero, Pi.zero_apply]
  ring

theorem norm_yMat_eq {d N : ℕ} (hN : 1 ≤ N) (σ : Fin d → Equiv.Perm (Fin N)) :
    ‖toEuclideanCLM (𝕜 := ℂ) (yMat σ)‖ = ‖adjPerp σ‖ := by
  set Y := toEuclideanCLM (𝕜 := ℂ) (yMat σ) with hY
  have hagree : ∀ x : OnesPerp N, Y x = (adjPerp σ x : EuclideanSpace ℂ (Fin N)) := by
    intro x; ext a
    rw [hY, toE_yMat_apply, adjPerp_coe_apply, (mem_onesPerp_iff _).1 x.2]
    simp
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    set K := OnesPerp N
    have hx : Y x = Y (K.orthogonalProjectionOnto x : EuclideanSpace ℂ (Fin N)) := by
      have hmem : x - K.starProjection x ∈ (ℂ ∙ onesVec N) := by
        have := K.sub_starProjection_mem_orthogonal x
        rwa [Submodule.orthogonal_orthogonal] at this
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have h0 : Y (x - K.starProjection x) = 0 := by
        rw [← hc, map_smul, hY, toE_yMat_onesVec hN, smul_zero]
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    rw [hx, hagree]
    calc ‖(adjPerp σ (K.orthogonalProjectionOnto x) : EuclideanSpace ℂ (Fin N))‖
        = ‖adjPerp σ (K.orthogonalProjectionOnto x)‖ := rfl
      _ ≤ ‖adjPerp σ‖ * ‖K.orthogonalProjectionOnto x‖ := (adjPerp σ).le_opNorm _
      _ ≤ ‖adjPerp σ‖ * ‖x‖ := mul_le_mul_of_nonneg_left
          (K.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖adjPerp σ x‖ = ‖Y x‖ := by rw [hagree]; rfl
      _ ≤ ‖Y‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ := Y.le_opNorm _
      _ = ‖Y‖ * ‖x‖ := rfl

/-! ### The complexification of `xSum` -/
theorem yMat_eq_map {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    yMat σ = (StrongConv.T38.xSum σ).map (algebraMap ℝ ℂ) := by
  ext a b
  simp only [yMat, StrongConv.T38.xSum, Matrix.map_apply, Matrix.sum_apply, zMat_entry,
    StrongConv.T38.xMat, Matrix.of_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem norm_yMat_eq_norm_xSum {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    ‖toEuclideanCLM (𝕜 := ℂ) (yMat σ)‖ = ‖StrongConv.T38.xSum σ‖ := by
  rw [yMat_eq_map, StrongConv.T38.norm_toEuclideanCLM_map_ofReal]

/-! ### The tail bound -/
theorem stub_apply : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (N d : ℕ), 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
    ∃ σ s v R : ℝ,
      ((Finset.univ.filter fun ω : Fin d → Equiv.Perm (Fin N) =>
        2 * σ + C₀ * (Real.sqrt v * Real.sqrt σ * Real.log N ^ ((3 : ℝ) / 4) +
          s * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
          R * t) < ‖toEuclideanCLM (𝕜 := ℂ) (yMat ω)‖).card : ℝ) /
          (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≤ 4 * N * Real.exp (-t) ∧
      0 ≤ σ ∧ σ ^ 2 ≤ 2 * d * N / (N - 1) ∧ s ≤ Real.sqrt (4 * d / (N - 1)) ∧
      0 ≤ v ∧ v ^ 2 ≤ 4 * d / (N - 1) ∧ 0 ≤ R ∧ R ≤ 4 := by
  obtain ⟨C₀, hC₀, H⟩ := StrongConv.T38.exists_tail
  refine ⟨C₀, hC₀, fun N d hN t ht => ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have h := H N d hN t ht
  refine ⟨Real.sqrt (2 * d * N / ((N : ℝ) - 1)), Real.sqrt (4 * d / ((N : ℝ) - 1)), 0, 4, ?_,
    Real.sqrt_nonneg _, ?_, le_rfl, le_rfl, ?_, by norm_num, le_rfl⟩
  · simp only [Real.sqrt_zero, zero_mul, zero_add, norm_yMat_eq_norm_xSum]
    exact h
  · rw [Real.sq_sqrt (by positivity)]
  · have : (0 : ℝ) ≤ 4 * d / ((N : ℝ) - 1) := by positivity
    simpa using this

/-! ### Assembly -/
theorem prob_ge {X : Type*} [Fintype X] [Nonempty X] (E P : X → Prop) [DecidablePred P]
    (h : ∀ x, ¬ P x → E x) :
    1 - ((Finset.univ.filter P).card : ℝ) / Fintype.card X ≤ uniformProb E := by
  classical
  unfold uniformProb
  have hpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  have h2 : (Finset.univ.filter (fun x => ¬ P x)).card ≤ (Finset.univ.filter E).card :=
    Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)
  rw [Finset.card_univ] at h1
  rw [one_sub_div hpos.ne', div_le_div_iff_of_pos_right hpos]
  have : ((Fintype.card X : ℕ) : ℝ) - (Finset.univ.filter P).card =
      (Finset.univ.filter (fun x => ¬ P x)).card := by
    rw [← h1]; push_cast; ring
  rw [this]; exact_mod_cast h2

theorem le_of_pow_le {X Y K : ℝ} {n : ℕ} (hn : n ≠ 0) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hK : 1 ≤ K)
    (h : X ^ n ≤ K * Y ^ n) : X ≤ K * Y := by
  have h' : X ^ n ≤ (K * Y) ^ n := h.trans (by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (le_self_pow₀ hK hn) (pow_nonneg hY n))
  exact (pow_le_pow_iff_left₀ hX (by positivity) hn).1 h'

theorem sq_bound {N d : ℝ} (hNr : 2 ≤ N) (hd0 : 0 ≤ d) :
    2 * d * N / (N - 1) ≤ (Real.sqrt (2 * d) * (1 + 2 / N)) ^ 2 := by
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  rw [mul_pow, Real.sq_sqrt (by positivity), div_le_iff₀ hN1]
  set x := 2 / N with hx
  have hxN : x * N = 2 := by rw [hx]; field_simp
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by linarith)]; exact hNr
  have e : (1 + x) ^ 2 * (N - 1) - N = 3 - 2 * x + x ^ 2 * (N - 1) := by
    linear_combination 2 * hxN
  have hpos : 0 ≤ (1 + x) ^ 2 * (N - 1) - N := by
    rw [e]; nlinarith [mul_nonneg (sq_nonneg x) hN1.le]
  nlinarith [mul_nonneg hd0 hpos]

/-- The constant. -/
def Cst (a C₀ : ℝ) : ℝ := 4 + C₀ * (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3) ^ 2 + 2 * (a + 3))

theorem threshold_le (a C₀ : ℝ) (ha : 0 < a) (hC₀ : 0 ≤ C₀) (N d : ℕ) (hN : 2 ≤ N) (hd : 1 ≤ d)
    (t σ s v R : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ (a + 3) * Real.log N)
    (hσ0 : 0 ≤ σ) (hσ : σ ^ 2 ≤ 2 * d * N / (N - 1)) (hs : s ≤ Real.sqrt (4 * d / (N - 1)))
    (hv0 : 0 ≤ v) (hv : v ^ 2 ≤ 4 * d / (N - 1)) (hR0 : 0 ≤ R) (hR : R ≤ 4) :
    2 * σ + C₀ * (Real.sqrt v * Real.sqrt σ * Real.log N ^ ((3 : ℝ) / 4) +
          s * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
          R * t) ≤ (1 + Cst a C₀ * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
          Cst a C₀ * Real.log N ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) +
          Cst a C₀ * Real.log N / (d : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * d)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN1 : (0 : ℝ) < N - 1 := by linarith only [hNr]
  set L := Real.log N with hLdef
  have hL : 1 / 2 ≤ L := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hNr
    linarith
  have hL0 : 0 ≤ L := by linarith only [hL]
  set p := L ^ ((3 : ℝ) / 4) with hp
  set q := (N : ℝ) ^ ((1 : ℝ) / 4) with hq
  set r := L ^ ((2 : ℝ) / 3) with hr
  set e := (d : ℝ) ^ ((1 : ℝ) / 6) with he
  set sd := Real.sqrt d with hsd
  have hp0 : 0 ≤ p := Real.rpow_nonneg hL0 _
  have hr0 : 0 ≤ r := Real.rpow_nonneg hL0 _
  have hq0 : 0 < q := by positivity
  have he0 : 0 < e := by positivity
  have hp4 : p ^ 4 = L ^ 3 := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  have hr3 : r ^ 3 = L ^ 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  have hq4 : q ^ 4 = N := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hd2 : (d : ℝ) ^ ((1 : ℝ) / 2) = sd := (Real.sqrt_eq_rpow _).symm
  have he3 : e ^ 3 = sd := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hsd, Real.sqrt_eq_rpow]; norm_num
  have hsd2 : sd ^ 2 = d := Real.sq_sqrt (by positivity)
  have hsd1 : 1 ≤ sd := by rw [hsd]; exact Real.one_le_sqrt.2 hdr
  have hsd0 : 0 < sd := by linarith only [hsd1]
  set A := 2 * Real.sqrt (2 * d) with hAdef
  have hA : 2 * sd ≤ A := by
    rw [hAdef, hsd]; gcongr; linarith
  have hA0 : 0 ≤ A := by positivity
  have hq1 : 1 ≤ q :=
    (pow_le_pow_iff_left₀ (by norm_num) hq0.le (by norm_num : (4 : ℕ) ≠ 0)).1
      (by rw [hq4]; norm_num; linarith)
  have hqN : q ≤ N := by
    have := le_self_pow₀ hq1 (by norm_num : (4 : ℕ) ≠ 0); rw [hq4] at this; exact this
  have hp_half : 1 / 2 ≤ p := by
    refine (pow_le_pow_iff_left₀ (by norm_num) hp0 (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
    rw [hp4]
    have h3 : ((1 : ℝ) / 2) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
    exact le_trans (by norm_num) h3
  have hdN2 : (0 : ℝ) ≤ (d : ℝ) * ((N : ℝ) - 2) :=
    mul_nonneg (by linarith only [hdr]) (by linarith only [hNr])
  have hd2N : (0 : ℝ) ≤ (d : ℝ) ^ 2 * (240 * (N : ℝ) - 256) :=
    mul_nonneg (sq_nonneg _) (by linarith only [hNr])
  have ha3 : 1 ≤ (a + 3) ^ 2 := one_le_pow₀ (by linarith only [ha])
  have hσ4 : σ ^ 2 ≤ 4 * d := by
    refine hσ.trans ?_
    rw [div_le_iff₀ hN1]; linarith only [hdN2]
  have hcov : 4 * (d : ℝ) / (N - 1) ≤ 8 * d / N := by
    rw [div_le_div_iff₀ hN1 (by linarith only [hNr])]; linarith only [hdN2]
  have hinvN : 1 / (N : ℝ) ≤ L := by
    rw [div_le_iff₀ (by linarith only [hNr])]
    have := mul_le_mul hL hNr (by norm_num) hL0
    norm_num at this ⊢; exact this
  have ht2 : t ^ 2 ≤ ((a + 3) * L) ^ 2 := pow_le_pow_left₀ ht0 ht 2
  have hP1 : 0 ≤ p / q := div_nonneg hp0 hq0.le
  have hP2 : 0 ≤ r / e := div_nonneg hr0 he0.le
  have hP3 : 0 ≤ L / sd := div_nonneg hL0 hsd0.le
  -- term 0
  have h0 : 2 * σ ≤ A + 4 * (p / q) * A := by
    have hNN := sq_bound (N := N) (d := d) hNr (by linarith only [hdr])
    have hσle : σ ≤ Real.sqrt (2 * d) * (1 + 2 / N) :=
      (pow_le_pow_iff_left₀ hσ0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 (hσ.trans hNN)
    have h2N : 2 / (N : ℝ) ≤ 4 * (p / q) := by
      have h1 : 1 / (N : ℝ) ≤ 1 / q := one_div_le_one_div_of_le hq0 hqN
      have h2 : 1 / q ≤ 2 * p / q := div_le_div_of_nonneg_right (by linarith only [hp_half]) hq0.le
      have : 2 / (N : ℝ) = 2 * (1 / N) := by ring
      rw [this, mul_div_assoc] at *
      linarith
    calc 2 * σ ≤ 2 * (Real.sqrt (2 * d) * (1 + 2 / N)) := by linarith
      _ ≤ 2 * (Real.sqrt (2 * d) * (1 + 4 * (p / q))) := by gcongr
      _ = A + 4 * (p / q) * A := by rw [hAdef]; ring
  -- term 1
  have h1 : Real.sqrt v * Real.sqrt σ * p ≤ 2 * (p / q) * A := by
    have hX : Real.sqrt v * Real.sqrt σ ≤ 1 * (4 * sd / q) := by
      refine le_of_pow_le (n := 4) (by norm_num) (by positivity) (by positivity) le_rfl ?_
      have e1 : (Real.sqrt v * Real.sqrt σ) ^ 4 = v ^ 2 * σ ^ 2 := by
        rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, Real.sq_sqrt hv0,
          Real.sq_sqrt hσ0]
      have e2 : (4 * sd / q) ^ 4 = 256 * (sd ^ 2) ^ 2 / q ^ 4 := by ring
      rw [e1, one_mul, e2, hsd2, hq4]
      calc v ^ 2 * σ ^ 2 ≤ (4 * d / (N - 1)) * (4 * d) :=
            mul_le_mul hv hσ4 (by positivity) (by positivity)
        _ ≤ 256 * (d : ℝ) ^ 2 / N := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ hN1 (by linarith only [hNr])]; linarith only [hd2N]
    calc Real.sqrt v * Real.sqrt σ * p ≤ 1 * (4 * sd / q) * p := by gcongr
      _ = 2 * (p / q) * (2 * sd) := by ring
      _ ≤ 2 * (p / q) * A := by gcongr
  -- term 2
  have h2 : s * Real.sqrt t ≤ (4 * (a + 3) ^ 2) * (p / q) * A := by
    have hX : Real.sqrt (4 * d / (N - 1)) * Real.sqrt t ≤
        (4 * (a + 3) ^ 2) * ((p / q) * (2 * sd)) := by
      refine le_of_pow_le (n := 4) (by norm_num) (by positivity) (by positivity) (by linarith only [ha3]) ?_
      have e1 : (Real.sqrt (4 * d / (N - 1)) * Real.sqrt t) ^ 4 =
          (4 * d / (N - 1)) ^ 2 * t ^ 2 := by
        rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, Real.sq_sqrt (by positivity),
          Real.sq_sqrt ht0]
      have e2 : ((p / q) * (2 * sd)) ^ 4 = p ^ 4 / q ^ 4 * 16 * (sd ^ 2) ^ 2 := by ring
      rw [e1, e2, hp4, hq4, hsd2]
      calc (4 * d / (N - 1)) ^ 2 * t ^ 2 ≤ (8 * d / N) ^ 2 * ((a + 3) * L) ^ 2 := by
            gcongr
        _ = 64 * (a + 3) ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * (1 / N) * (1 / N) := by ring
        _ ≤ 64 * (a + 3) ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * L * (1 / N) := by gcongr
        _ = 4 * (a + 3) ^ 2 * (L ^ 3 / N * 16 * (d : ℝ) ^ 2) := by ring
    calc s * Real.sqrt t ≤ Real.sqrt (4 * d / (N - 1)) * Real.sqrt t := by gcongr
      _ ≤ (4 * (a + 3) ^ 2) * ((p / q) * (2 * sd)) := hX
      _ ≤ (4 * (a + 3) ^ 2) * ((p / q) * A) := by gcongr
      _ = (4 * (a + 3) ^ 2) * (p / q) * A := by ring
  -- term 3
  have h3 : R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) ≤
      (2 * (a + 3) ^ 2) * (r / e) * A := by
    have hX : R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) ≤
        (2 * (a + 3) ^ 2) * ((r / e) * (2 * sd)) := by
      refine le_of_pow_le (n := 3) (by norm_num) (by positivity) (by positivity) (by linarith only [ha3]) ?_
      have e1 : (R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3)) ^ 3 =
          R * σ ^ 2 * t ^ 2 := by
        rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (σ ^ ((2 : ℝ) / 3)),
          ← Real.rpow_natCast (t ^ ((2 : ℝ) / 3)), ← Real.rpow_mul hR0, ← Real.rpow_mul hσ0,
          ← Real.rpow_mul ht0]
        norm_num
      have e2 : ((r / e) * (2 * sd)) ^ 3 = r ^ 3 / e ^ 3 * 8 * sd ^ 3 := by ring
      rw [e1, e2, hr3, he3]
      have e3 : L ^ 2 / sd * 8 * sd ^ 3 = 8 * L ^ 2 * sd ^ 2 := by field_simp
      rw [e3, hsd2]
      calc R * σ ^ 2 * t ^ 2 ≤ 4 * (4 * d) * ((a + 3) * L) ^ 2 := by gcongr
        _ = 2 * (a + 3) ^ 2 * (8 * L ^ 2 * d) := by ring
    calc _ ≤ (2 * (a + 3) ^ 2) * ((r / e) * (2 * sd)) := hX
      _ ≤ (2 * (a + 3) ^ 2) * ((r / e) * A) := by gcongr
      _ = _ := by ring
  -- term 4
  have h4 : R * t ≤ (2 * (a + 3)) * (L / sd) * A := by
    calc R * t ≤ 4 * ((a + 3) * L) := by gcongr
      _ = (2 * (a + 3)) * (L / sd) * (2 * sd) := by field_simp; ring
      _ ≤ (2 * (a + 3)) * (L / sd) * A := by gcongr
  -- combine
  rw [hd2, mul_div_assoc, mul_div_assoc, mul_div_assoc]
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) hC₀
  have key : (1 + Cst a C₀ * (p / q) + Cst a C₀ * (r / e) + Cst a C₀ * (L / sd)) * A =
      A + 4 * (p / q) * A + C₀ * (2 * (p / q) * A + 4 * (a + 3) ^ 2 * (p / q) * A +
        2 * (a + 3) ^ 2 * (r / e) * A + 2 * (a + 3) * (L / sd) * A) +
      C₀ * ((2 * (a + 3) ^ 2 + 2 * (a + 3)) * (p / q) * A +
        (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3)) * (r / e) * A +
        (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3) ^ 2) * (L / sd) * A) +
      4 * (r / e) * A + 4 * (L / sd) * A := by
    simp only [Cst]; ring
  have hextra : 0 ≤ C₀ * ((2 * (a + 3) ^ 2 + 2 * (a + 3)) * (p / q) * A +
        (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3)) * (r / e) * A +
        (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3) ^ 2) * (L / sd) * A) := by
    have : 0 ≤ a + 3 := by linarith only [ha]
    positivity
  have hx2 : 0 ≤ 4 * (r / e) * A := by positivity
  have hx3 : 0 ≤ 4 * (L / sd) * A := by positivity
  rw [key]
  linarith only [h0, hsum, hextra, hx2, hx3]

theorem prob_ge' {X : Type*} [Fintype X] [Nonempty X] (E P : X → Prop) [DecidablePred P]
    (h : ∀ x, ¬ P x → E x) (c : ℝ)
    (hc : ((Finset.univ.filter P).card : ℝ) / Fintype.card X ≤ c) : 1 - c ≤ uniformProb E :=
  le_trans (by linarith) (prob_ge E P h)

theorem prob_norm_adjPerp_le_highDegree_ge_dev (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d →
      1 - (N : ℝ) ^ (-a) ≤ uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ‖adjPerp σ‖ ≤ (1 + C * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
          C * Real.log N ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) +
          C * Real.log N / (d : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * d))) := by
  obtain ⟨C₀, hC₀, H⟩ := stub_apply
  refine ⟨Cst a C₀, by unfold Cst; positivity, fun N d hN hd => ?_⟩
  rcases (show N = 1 ∨ 2 ≤ N by omega) with rfl | hN2
  · simp only [Nat.cast_one, Real.one_rpow, sub_self]
    unfold uniformProb
    positivity
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set t := (a + 1) * Real.log N + Real.log 4 with htdef
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log N := by linarith
  have ht0 : 0 ≤ t := by
    rw [htdef, hlog4]; have := mul_nonneg (by linarith : (0 : ℝ) ≤ a + 1) hL; linarith
  have ht : t ≤ (a + 3) * Real.log N := by
    rw [htdef, hlog4]; nlinarith
  have hexp : 4 * (N : ℝ) * Real.exp (-t) = (N : ℝ) ^ (-a) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
    have hNe : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log (by linarith)).symm
    calc 4 * (N : ℝ) * Real.exp (-t)
        = Real.exp (Real.log 4) * Real.exp (Real.log N) * Real.exp (-t) := by
          rw [← h4, ← hNe]
      _ = Real.exp (Real.log N * -a) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [htdef]; ring
  obtain ⟨σ, s, v, R, hP, hσ0, hσ, hs, hv0, hv, hR0, hR⟩ := H N d hN2 t ht0
  have hT := threshold_le a C₀ ha hC₀.le N d hN2 hd t σ s v R ht0 ht hσ0 hσ hs hv0 hv hR0 hR
  rw [← hexp]
  refine prob_ge' _ _ ?_ _ hP
  intro ω hω
  rw [not_lt, norm_yMat_eq hN] at hω
  exact hω.trans hT

end StrongConv.T38.Up
end
end

theorem solution (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d →
      1 - (N : ℝ) ^ (-a) ≤ StrongConv.uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ‖StrongConv.adjPerp σ‖ ≤ (1 + C * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
          C * Real.log N ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) +
          C * Real.log N / (d : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * d))) :=
  StrongConv.T38.Up.prob_norm_adjPerp_le_highDegree_ge_dev a ha
