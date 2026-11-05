-- Prove2me | solution 1 for abs_quad_form_entry_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:17:07.864662+00:00
-- url     : https://prove2.me/submissions/20e89da5-7307-4843-9e59-cda356868d6d

import Mathlib
/-
# Leaf B — `brick-errprop`: error propagation and perturbation bounds

Supporting brick for the certified SDP lower-value program of the 0.53 Quantum Max-Cut leaf
(`91ee3bff`). It supplies the *numerical robustness* layer that the exact-arithmetic bricks need
in order to turn a certificate computed from finitely-precise (dyadic) data into a statement about
the exact real/rational object.

Compile (in the Prove2me workspace): `lake env lean Solutions/Check_errprop.lean`.
Imports: `Mathlib` only. No `sorry`, no new axioms.

## What is proved

**1. Scalar error-budget algebra** (any `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`,
hence both `ℚ` and `ℝ`):
* `abs_sub_le_add_of_abs_sub_le` — budgets compose: `|x-y| ≤ ε`, `|y-z| ≤ δ` ⟹ `|x-z| ≤ ε+δ`.
* `abs_mul_sub_mul_le` — product rule `|xy - x'y'| ≤ εx|y| + |x'|εy`.
* `pos_of_abs_sub_le_lt` — a margin survives: `|x-y| ≤ ε < x` ⟹ `0 < y`.
* `abs_sum_sub_sum_le` — budgets add over finsets.
* `abs_sub_le_natCast_mul_of_steps` — a chain of `m` steps each losing `≤ ε` loses `≤ m·ε`
  (the shape of every iterative numerical subroutine).

**2. The `ℓ¹`–`ℓ²` inequality** (`l1_sq_le_card_mul_l2sq`): `(∑ᵢ|zᵢ|)² ≤ n · ∑ᵢ zᵢ²`.
This is the Cauchy–Schwarz step that converts an entrywise sup-norm bound into an operator bound.

**3. Quadratic forms** of `Matrix (Fin n) (Fin n) R`: `quadForm A z = zᵀ (A z)`, with the double-sum
expansion, and linearity in `A` (`quadForm_add/_sub/_neg/_smul/_zero`), `quadForm_transpose`,
`quadForm_one`.

**4. Entrywise perturbation bounds — the main output**:
* `abs_quadForm_le_of_entry_le` : `(∀ i j, |Δᵢⱼ| ≤ ε) ⟹ |zᵀΔz| ≤ ε (∑ᵢ|zᵢ|)²`.
* `abs_quadForm_le_of_entry_le_card` : `… ⟹ |zᵀΔz| ≤ ε · n · ∑ᵢ zᵢ²`.
  (This is exactly the estimate `brick-certpsd` needs for its residual term `R`.)
* `quadForm_add_perturb_ge` : a margin degrades by the perturbation,
  `zᵀ(A+Δ)z ≥ (δ − ε·n)‖z‖²` when `zᵀAz ≥ δ‖z‖²`.

**5. Positive semidefiniteness** (generic in `R` with `[StarRing R] [TrivialStar R]`, so it applies
to `ℚ` — the exact-certificate notion — and to `ℝ`):
* `posSemidef_of_margin` : symmetric + `zᵀAz ≥ δ‖z‖²` with `δ ≥ 0` ⟹ `A.PosSemidef`.
* `posSemidef_add_of_margin` : `A + Δ` is PSD when `Δ` is symmetric, entrywise `≤ ε`, `ε·n ≤ δ`.
* `posSemidef_of_entry_near` : the pipeline shape — a computed matrix `M'` entrywise within `ε`
  of an exact matrix `M` with margin `δ` is PSD.
* `isSymm_diagonal`.

**6. The duality-gap budget**:
* `abs_sum_mul_sub_le` — a linear functional is Lipschitz in its argument (sup-norm budget).
* `abs_trace_mul_le` — the trace pairing: `|tr(ΔX)| ≤ ε · ∑ᵢⱼ|Xᵢⱼ|` for entrywise `|Δᵢⱼ| ≤ ε`.
* `gap_budget` — the assembled statement: if the dual vector `y` and the constraint matrix `A` are
  known only within budgets `εy`, `εA`, then the computed duality gap `∑ᵢ yᵢ + tr(A X)` differs from
  the exact gap by at most `εA · ∑ᵢⱼ|Xᵢⱼ| + n · εy`.

**7. Size bounds for PSD matrices** (all over `ℝ`, from the Gram factorisation
`Matrix.posSemidef_iff_eq_sum_vecMulVec` and Cauchy–Schwarz over the Gram rank):
* `sq_entry_le_diag_mul` : `X.PosSemidef → Xᵢⱼ ^ 2 ≤ Xᵢᵢ * Xⱼⱼ` (the `2 × 2` minor bound);
* `two_mul_abs_entry_le_diag_add` : `2 |Xᵢⱼ| ≤ Xᵢᵢ + Xⱼⱼ` (AM–GM);
* `sum_abs_entry_le_card_mul_trace` : `X.PosSemidef → ∑ᵢⱼ |Xᵢⱼ| ≤ n · tr X`;
* `abs_trace_mul_le_of_posSemidef` : `|tr(Δ X)| ≤ ε · n · tr X` for entrywise `|Δᵢⱼ| ≤ ε`, `ε ≥ 0`;
* `gap_budget_psd` : the gap budget in terms of the primal trace,
  `|Δgap| ≤ εA · n · tr X + n · εy`.

Two kernel-checked concrete instances at the end (`ℚ` and `ℝ`) exercise the main lemmas with
numerals, and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`.

## Notes for the assembly
* Everything is stated for `n : ℕ` with indices `Fin n`, matching Mathlib's `Matrix` API, so it
  composes directly with `Matrix.PosSemidef` and with any Gram/LDL certificate produced over `ℚ`.
* `commRing_nf`/`ring`/`nlinarith` do the work; there is no custom syntax, no macro, no notation.
* The `ℚ` form of `posSemidef_*` gives `q(z) ≥ 0` for **rational** `z` only. Bridging that to `ℝ`
  (density of `ℚ` in `ℝ` + continuity of the quadratic form) is *not* done here.
-/


namespace LeafB.ErrProp

open Matrix

section Scalar

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

theorem abs_sub_le_add_of_abs_sub_le {x y z ε δ : R}
    (h1 : |x - y| ≤ ε) (h2 : |y - z| ≤ δ) : |x - z| ≤ ε + δ := by
  have h : x - z = (x - y) + (y - z) := by ring
  rw [h]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem abs_mul_sub_mul_le {x x' y y' εx εy : R}
    (hx : |x - x'| ≤ εx) (hy : |y - y'| ≤ εy) :
    |x * y - x' * y'| ≤ εx * |y| + |x'| * εy := by
  have h : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
  rw [h]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg y)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg x')

theorem pos_of_abs_sub_le_lt {x y ε : R} (h : |x - y| ≤ ε) (hlt : ε < x) : 0 < y := by
  have h2 : x - y ≤ ε := (abs_sub_le_iff.1 h).1
  linarith

theorem abs_sum_sub_sum_le {ι : Type*} (s : Finset ι) (f g ε : ι → R)
    (h : ∀ i ∈ s, |f i - g i| ≤ ε i) :
    |∑ i ∈ s, f i - ∑ i ∈ s, g i| ≤ ∑ i ∈ s, ε i := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)

theorem l1_sq_le_card_mul_l2sq {ι : Type*} [Fintype ι] (z : ι → R) :
    (∑ i, |z i|) ^ 2 ≤ (Fintype.card ι : R) * ∑ i, z i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset ι))
    (f := fun i => |z i|) (g := fun _ => (1 : R))
  simpa [sq_abs, Finset.card_univ, Finset.sum_const, nsmul_eq_mul, mul_comm] using h

end Scalar

section QuadForm

variable {R : Type*} [Field R]

/-- The quadratic form `z ↦ zᵀ A z` of a square matrix, as a plain function. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) : R := z ⬝ᵥ A.mulVec z

theorem quadForm_eq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm A z = ∑ i, ∑ j, A i j * z i * z j := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quadForm_zero {n : ℕ} (z : Fin n → R) : quadForm (0 : Matrix (Fin n) (Fin n) R) z = 0 := by
  simp [quadForm_eq_sum]

theorem quadForm_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm (A + B) z = quadForm A z + quadForm B z := by
  simp only [quadForm_eq_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.add_apply]
  ring

theorem quadForm_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm (-A) z = -quadForm A z := by
  simp only [quadForm_eq_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.neg_apply]
  ring

theorem quadForm_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm (A - B) z = quadForm A z - quadForm B z := by
  rw [sub_eq_add_neg, quadForm_add, quadForm_neg, sub_eq_add_neg]

theorem quadForm_smul {n : ℕ} (c : R) (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm (c • A) z = c * quadForm A z := by
  simp only [quadForm_eq_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem quadForm_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm Aᵀ z = quadForm A z := by
  simp only [quadForm_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply]
  ring

end QuadForm

end LeafB.ErrProp

namespace LeafB.ErrProp

open Matrix

section Perturbation

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Entrywise perturbation bound for a quadratic form, in `ℓ¹` form. -/
theorem abs_quadForm_le_of_entry_le {n : ℕ} {Δ : Matrix (Fin n) (Fin n) R} {ε : R}
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    |quadForm Δ z| ≤ ε * (∑ i, |z i|) ^ 2 := by
  rw [quadForm_eq_sum]
  have step1 : |∑ i, ∑ j, Δ i j * z i * z j| ≤ ∑ i, ∑ j, |Δ i j| * |z i| * |z j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [abs_mul, abs_mul])
  refine step1.trans ?_
  have step2 : ∑ i, ∑ j, |Δ i j| * |z i| * |z j| ≤ ∑ i, ∑ j, ε * |z i| * |z j| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hΔ i j) (abs_nonneg _)) (abs_nonneg _)
  refine step2.trans ?_
  rw [← Finset.sum_mul_sum (f := fun i => ε * |z i|) (g := fun j => |z j|), ← Finset.mul_sum]
  exact le_of_eq (by ring)

/-- Entrywise perturbation bound for a quadratic form: `|zᵀΔz| ≤ ε·n·∑zᵢ²`. -/
theorem abs_quadForm_le_of_entry_le_card {n : ℕ} {Δ : Matrix (Fin n) (Fin n) R} {ε : R}
    (hε : 0 ≤ ε) (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    |quadForm Δ z| ≤ ε * (n : R) * ∑ i, z i ^ 2 := by
  refine (abs_quadForm_le_of_entry_le hΔ z).trans ?_
  have hle : (∑ i, |z i|) ^ 2 ≤ (n : R) * ∑ i, z i ^ 2 := by
    simpa using l1_sq_le_card_mul_l2sq (R := R) z
  calc ε * (∑ i, |z i|) ^ 2 ≤ ε * ((n : R) * ∑ i, z i ^ 2) :=
        mul_le_mul_of_nonneg_left hle hε
    _ = ε * (n : R) * ∑ i, z i ^ 2 := by ring

/-- A margin survives an entrywise perturbation: the perturbed quadratic form still dominates
`(δ - ε·n)‖z‖²`. -/
theorem quadForm_add_perturb_ge {n : ℕ} {A Δ : Matrix (Fin n) (Fin n) R} {δ ε : R}
    (hε : 0 ≤ ε) (hA : ∀ z : Fin n → R, δ * ∑ i, z i ^ 2 ≤ quadForm A z)
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    (δ - ε * (n : R)) * ∑ i, z i ^ 2 ≤ quadForm (A + Δ) z := by
  have hb := abs_quadForm_le_of_entry_le_card hε hΔ z
  have h1 : -quadForm Δ z ≤ ε * (n : R) * ∑ i, z i ^ 2 := by linarith [(abs_le.1 hb).1]
  rw [quadForm_add]
  nlinarith [hA z]

/-- Pointwise form: entrywise perturbation costs at most `ε·n·∑zᵢ²` on the negative side. -/
theorem quadForm_add_entry_le_ge {n : ℕ} {A Δ : Matrix (Fin n) (Fin n) R} {ε : R}
    (hε : 0 ≤ ε) (hA : ∀ z : Fin n → R, 0 ≤ quadForm A z)
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    -(ε * (n : R) * ∑ i, z i ^ 2) ≤ quadForm (A + Δ) z := by
  have h := quadForm_add_perturb_ge (A := A) (Δ := Δ) (δ := 0) hε (by simpa using hA) hΔ z
  simpa using h

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `quadForm` of the identity is the squared norm. -/
theorem quadForm_one {n : ℕ} (z : Fin n → R) :
    quadForm (1 : Matrix (Fin n) (Fin n) R) z = ∑ i, z i ^ 2 := by
  simp only [quadForm, Matrix.one_mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

end Perturbation

end LeafB.ErrProp

namespace LeafB.ErrProp

open Matrix

section PSD

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R]

/-- A symmetric matrix whose quadratic form dominates `δ‖z‖²` with `δ ≥ 0` is positive
semidefinite. Works over `ℚ` (the exact-certificate notion) and over `ℝ`. -/
theorem posSemidef_of_margin {n : ℕ} {A : Matrix (Fin n) (Fin n) R} {δ : R}
    (hAsymm : A.IsSymm) (hA : ∀ z : Fin n → R, δ * ∑ i, z i ^ 2 ≤ quadForm A z)
    (hδ : 0 ≤ δ) : A.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun z => ?_⟩
  · exact Matrix.isHermitian_iff_isSymm.2 hAsymm
  · have hz' : star z = z := by funext i; exact star_trivial (z i)
    rw [hz']
    change 0 ≤ quadForm A z
    have hz : (0 : R) ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [hA z, mul_nonneg hδ hz]

/-- **Entrywise robustness of a PSD margin.** If `zᵀAz ≥ δ‖z‖²` and every entry of the symmetric
perturbation `Δ` is at most `ε` in absolute value, and `ε·n ≤ δ`, then `A + Δ` is positive
semidefinite. -/
theorem posSemidef_add_of_margin {n : ℕ} {A Δ : Matrix (Fin n) (Fin n) R} {δ ε : R}
    (hAsymm : A.IsSymm) (hA : ∀ z : Fin n → R, δ * ∑ i, z i ^ 2 ≤ quadForm A z)
    (hΔsymm : Δ.IsSymm) (hε : 0 ≤ ε) (hΔ : ∀ i j, |Δ i j| ≤ ε)
    (hlt : ε * (n : R) ≤ δ) : (A + Δ).PosSemidef :=
  posSemidef_of_margin (IsSymm.add hAsymm hΔsymm)
    (fun z => quadForm_add_perturb_ge (A := A) (Δ := Δ) (δ := δ) hε hA hΔ z)
    (by linarith)

/-- **Pipeline shape.** If the exact matrix `M` has a positive margin and the computed matrix `M'`
is entrywise within `ε` of it, then `M'` is positive semidefinite. This is the form in which the
perturbation bound is consumed by a certified-solver assembly (`M = diag y + A`). -/
theorem posSemidef_of_entry_near {n : ℕ} {M M' : Matrix (Fin n) (Fin n) R} {δ ε : R}
    (hMsymm : M.IsSymm) (hM : ∀ z : Fin n → R, δ * ∑ i, z i ^ 2 ≤ quadForm M z)
    (hM'symm : M'.IsSymm) (hε : 0 ≤ ε) (hΔ : ∀ i j, |M i j - M' i j| ≤ ε)
    (hlt : ε * (n : R) ≤ δ) : M'.PosSemidef := by
  have hsub : M + (M' - M) = M' := by abel
  rw [← hsub]
  exact posSemidef_add_of_margin (Δ := M' - M) hMsymm hM (IsSymm.sub hM'symm hMsymm) hε
    (fun i j => by simpa [abs_sub_comm] using hΔ i j) hlt

omit [LinearOrder R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R] in
/-- The diagonal matrix is symmetric. -/
theorem isSymm_diagonal {n : ℕ} (y : Fin n → R) : (Matrix.diagonal y).IsSymm := by
  simp [Matrix.IsSymm, Matrix.diagonal_transpose]

end PSD

section Lipschitz

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A linear functional is Lipschitz in its argument w.r.t. the sup-norm budget. -/
theorem abs_sum_mul_sub_le {ι : Type*} [Fintype ι] (y b b' : ι → R) {m : R}
    (h : ∀ i, |b i - b' i| ≤ m) :
    |∑ i, y i * b i - ∑ i, y i * b' i| ≤ (∑ i, |y i|) * m := by
  have hre : ∑ i, y i * b i - ∑ i, y i * b' i = ∑ i, y i * (b i - b' i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hre]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |y i * (b i - b' i)| ≤ ∑ i, |y i| * m := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = (∑ i, |y i|) * m := (Finset.sum_mul _ _ _).symm

/-- **The trace pairing is Lipschitz in the entrywise sup-norm**: an entrywise perturbation of
`Δ` by at most `ε` changes `tr(ΔX)` by at most `ε · ∑ᵢⱼ |Xᵢⱼ|`. -/
theorem abs_trace_mul_le {n : ℕ} {Δ X : Matrix (Fin n) (Fin n) R} {ε : R}
    (hΔ : ∀ i j, |Δ i j| ≤ ε) :
    |Matrix.trace (Δ * X)| ≤ ε * ∑ i, ∑ j, |X i j| := by
  have htr : Matrix.trace (Δ * X) = ∑ i, ∑ j, Δ i j * X j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [htr]
  have step1 : |∑ i, ∑ j, Δ i j * X j i| ≤ ∑ i, ∑ j, |Δ i j| * |X j i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [abs_mul])
  have step2 : ∑ i, ∑ j, |Δ i j| * |X j i| ≤ ∑ i, ∑ j, ε * |X j i| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right (hΔ i j) (abs_nonneg _)
  refine (step1.trans step2).trans ?_
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]

/-- Telescoping error budgets: `m` steps each losing at most `ε` lose at most `m·ε` in total. -/
theorem abs_sub_le_natCast_mul_of_steps {x : ℕ → R} {ε : R} {m : ℕ}
    (h : ∀ k, k < m → |x (k + 1) - x k| ≤ ε) : |x m - x 0| ≤ (m : R) * ε := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : |x m - x 0| ≤ (m : R) * ε := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have h2 : |x (m + 1) - x m| ≤ ε := h m (Nat.lt_succ_self m)
    calc |x (m + 1) - x 0| ≤ (m : R) * ε + ε := by
          have := abs_sub_le_add_of_abs_sub_le (x := x (m + 1)) (y := x m) (z := x 0)
            (δ := (m : R) * ε) h2 h1
          linarith
      _ = ((m + 1 : ℕ) : R) * ε := by push_cast; ring

end Lipschitz

end LeafB.ErrProp

namespace LeafB.ErrProp

open Matrix

section PSDBounds

/-- The `2 × 2` minor bound for a positive semidefinite matrix: `Xᵢⱼ² ≤ Xᵢᵢ·Xⱼⱼ`.

Proved from the Gram factorisation `X = ∑ₖ vₖ vₖᵀ`
(`Matrix.posSemidef_iff_eq_sum_vecMulVec`) and Cauchy–Schwarz over `k`. -/
theorem sq_entry_le_diag_mul {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (i j : Fin n) : X i j ^ 2 ≤ X i i * X j j := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  have hentry : ∀ a b : Fin n, (∑ k, vecMulVec (v k) (star (v k))) a b = ∑ k, v k a * v k b := by
    intro a b
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial]
  rw [hentry i j, hentry i i, hentry j j]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin m)))
    (f := fun k => v k i) (g := fun k => v k j)
  simpa [sq] using h

/-- For a positive semidefinite matrix, `2|Xᵢⱼ| ≤ Xᵢᵢ + Xⱼⱼ` (AM–GM on the `2 × 2` minor). -/
theorem two_mul_abs_entry_le_diag_add {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (i j : Fin n) : 2 * |X i j| ≤ X i i + X j j := by
  have hsq : X i j ^ 2 ≤ X i i * X j j := sq_entry_le_diag_mul hX i j
  have hi : 0 ≤ X i i := hX.diag_nonneg
  have hj : 0 ≤ X j j := hX.diag_nonneg
  have h2 : (2 * |X i j|) ^ 2 ≤ (X i i + X j j) ^ 2 := by
    have habs : |X i j| ^ 2 = X i j ^ 2 := sq_abs _
    nlinarith [sq_nonneg (X i i - X j j)]
  have h4 : abs (2 * abs (X i j)) ≤ abs (X i i + X j j) := sq_le_sq.mp h2
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * abs (X i j) by positivity),
    abs_of_nonneg (show (0 : ℝ) ≤ X i i + X j j by linarith)] at h4
  exact h4

/-- **Entrywise `ℓ¹` size of a PSD matrix**: `∑ᵢⱼ |Xᵢⱼ| ≤ n · tr X`. -/
theorem sum_abs_entry_le_card_mul_trace {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) : ∑ i, ∑ j, |X i j| ≤ (n : ℝ) * Matrix.trace X := by
  have hb : ∀ i j : Fin n, |X i j| ≤ (X i i + X j j) / 2 := by
    intro i j
    have h := two_mul_abs_entry_le_diag_add hX i j
    linarith
  have hstep : ∀ i : Fin n, ∑ j : Fin n, ((X i i + X j j) / 2)
      = (n : ℝ) * X i i / 2 + Matrix.trace X / 2 := by
    intro i
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_fin, add_div]
    rw [show Matrix.trace X = ∑ x : Fin n, X x x from rfl]
  have hstep2 : ∑ i : Fin n, ((n : ℝ) * X i i / 2 + Matrix.trace X / 2)
      = (n : ℝ) * Matrix.trace X := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ i : Fin n, (n : ℝ) * X i i / 2 = (n : ℝ) * Matrix.trace X / 2 := by
      rw [← Finset.sum_div]
      congr 1
      exact (Finset.mul_sum (s := Finset.univ) (f := fun i => X i i) (a := (n : ℝ))).symm
    have h2 : ∑ _i : Fin n, (Matrix.trace X / 2) = (n : ℝ) * (Matrix.trace X / 2) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h1, h2]
    ring
  have hsplit : ∑ i, ∑ j, ((X i i + X j j) / 2) = (n : ℝ) * Matrix.trace X := by
    simp only [hstep]
    exact hstep2
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j).trans ?_
  rw [hsplit]

/-- **Sharp trace-pairing budget**: for a PSD primal matrix `X`, an entrywise perturbation of the
constraint matrix by `ε ≥ 0` moves `tr(A X)` by at most `ε · n · tr X`. -/
theorem abs_trace_mul_le_of_posSemidef {n : ℕ} {Δ X : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ}
    (hX : X.PosSemidef) (hε : 0 ≤ ε) (hΔ : ∀ i j, |Δ i j| ≤ ε) :
    |Matrix.trace (Δ * X)| ≤ ε * ((n : ℝ) * Matrix.trace X) := by
  have h1 := abs_trace_mul_le (Δ := Δ) (X := X) (ε := ε) hΔ
  have h2 := sum_abs_entry_le_card_mul_trace hX
  have h3 : ε * (∑ i, ∑ j, |X i j|) ≤ ε * ((n : ℝ) * Matrix.trace X) :=
    mul_le_mul_of_nonneg_left h2 hε
  linarith

/-- The gap budget in the PSD case: `εA · n · tr X + n · εy` controls the computed duality gap. -/
theorem gap_budget_psd {n : ℕ} {A A' X : Matrix (Fin n) (Fin n) ℝ} {y y' : Fin n → ℝ}
    {εA εy : ℝ} (hX : X.PosSemidef) (hεA : 0 ≤ εA)
    (hA : ∀ i j, |A i j - A' i j| ≤ εA) (hy : ∀ i, |y i - y' i| ≤ εy) :
    |(∑ i, y i + Matrix.trace (A * X)) - (∑ i, y' i + Matrix.trace (A' * X))|
      ≤ εA * ((n : ℝ) * Matrix.trace X) + (n : ℝ) * εy := by
  have h1 : |Matrix.trace ((A - A') * X)| ≤ εA * ((n : ℝ) * Matrix.trace X) :=
    abs_trace_mul_le_of_posSemidef hX hεA hA
  have key : (∑ i, y i + Matrix.trace (A * X)) - (∑ i, y' i + Matrix.trace (A' * X))
      = (∑ i, y i - ∑ i, y' i) + Matrix.trace ((A - A') * X) := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
    ring
  rw [key]
  have h2 : |∑ i, y i - ∑ i, y' i| ≤ (n : ℝ) * εy := by
    have h := abs_sum_mul_sub_le (fun _ : Fin n => (1 : ℝ)) y y' hy
    simpa using h
  calc |(∑ i, y i - ∑ i, y' i) + Matrix.trace ((A - A') * X)|
      ≤ |∑ i, y i - ∑ i, y' i| + |Matrix.trace ((A - A') * X)| := abs_add_le _ _
    _ ≤ (n : ℝ) * εy + εA * ((n : ℝ) * Matrix.trace X) := add_le_add h2 h1
    _ = εA * ((n : ℝ) * Matrix.trace X) + (n : ℝ) * εy := by ring

end PSDBounds

end LeafB.ErrProp

namespace LeafB.ErrProp

open Matrix

section GapBudget

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Duality-gap budget.** The SDP gap of a certified pair is `∑ yᵢ + tr(A X)` (with `X` the
primal matrix). If the data `(A, y)` is only known to within an entrywise budget `εA` and a
linear budget `εy`, then the computed gap differs from the exact gap by at most
`εA · ∑ᵢⱼ |Xᵢⱼ| + n · εy`. -/
theorem gap_budget {n : ℕ} {A A' X : Matrix (Fin n) (Fin n) R} {y y' : Fin n → R}
    {εA εy : R} (hA : ∀ i j, |A i j - A' i j| ≤ εA) (hy : ∀ i, |y i - y' i| ≤ εy) :
    |(∑ i, y i + Matrix.trace (A * X)) - (∑ i, y' i + Matrix.trace (A' * X))|
      ≤ εA * (∑ i, ∑ j, |X i j|) + (n : R) * εy := by
  have key : (∑ i, y i + Matrix.trace (A * X)) - (∑ i, y' i + Matrix.trace (A' * X))
      = (∑ i, y i - ∑ i, y' i) + Matrix.trace ((A - A') * X) := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
    ring
  rw [key]
  have h2 : |∑ i, y i - ∑ i, y' i| ≤ (n : R) * εy := by
    have h := abs_sum_mul_sub_le (fun _ : Fin n => (1 : R)) y y' hy
    simpa using h
  have h1 : |Matrix.trace ((A - A') * X)| ≤ εA * ∑ i, ∑ j, |X i j| := abs_trace_mul_le hA
  calc |(∑ i, y i - ∑ i, y' i) + Matrix.trace ((A - A') * X)|
      ≤ |∑ i, y i - ∑ i, y' i| + |Matrix.trace ((A - A') * X)| := abs_add_le _ _
    _ ≤ (n : R) * εy + εA * (∑ i, ∑ j, |X i j|) := add_le_add h2 h1
    _ = εA * (∑ i, ∑ j, |X i j|) + (n : R) * εy := by ring

end GapBudget

section Instances

/-- The ℚ-instance: the exact-arithmetic pipeline gets the entrywise quadratic-form bound. -/
theorem abs_quadForm_le_rat (n : ℕ) (Δ : Matrix (Fin n) (Fin n) ℚ) (ε : ℚ) (hε : 0 ≤ ε)
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → ℚ) :
    |quadForm Δ z| ≤ ε * (n : ℚ) * ∑ i, z i ^ 2 :=
  abs_quadForm_le_of_entry_le_card hε hΔ z

/-- The ℝ-instance, same statement. -/
theorem abs_quadForm_le_real (n : ℕ) (Δ : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → ℝ) :
    |quadForm Δ z| ≤ ε * (n : ℝ) * ∑ i, z i ^ 2 :=
  abs_quadForm_le_of_entry_le_card hε hΔ z

/-- Concrete ℚ check, kernel-checked: a `2 × 2` matrix all of whose entries are `1/10` has
quadratic form bounded by `(1/10)·2·∑ zᵢ²`. -/
example : |quadForm (fun _ _ : Fin 2 => (1 / 10 : ℚ)) (fun _ => 1)|
    ≤ (1 / 10 : ℚ) * (2 : ℚ) * ∑ _ : Fin 2, (1 : ℚ) ^ 2 :=
  abs_quadForm_le_rat 2 _ (1 / 10) (by norm_num) (fun _ _ => by norm_num) _

/-- Concrete ℝ check: `5 • 1 + Δ` is positive semidefinite for every symmetric `Δ` with entries
at most `1/10` in absolute value (margin `5 - 2·(1/10) = 24/5 > 0`). -/
example (Δ : Matrix (Fin 2) (Fin 2) ℝ) (hΔsymm : Δ.IsSymm)
    (hΔ : ∀ i j, |Δ i j| ≤ 1 / 10) :
    ((5 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Δ).PosSemidef := by
  have hmargin : ∀ z : Fin 2 → ℝ,
      (5 : ℝ) * ∑ i, z i ^ 2 ≤ quadForm ((5 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) z := by
    intro z
    rw [quadForm_smul, quadForm_one]
  refine posSemidef_add_of_margin (δ := 5) (ε := 1 / 10) ?_ hmargin hΔsymm (by norm_num) hΔ ?_
  · simp [Matrix.IsSymm]
  · norm_num

/-- Concrete ℚ check: `4 • 1 + Δ` is positive semidefinite over `ℚ` for every rational symmetric
`Δ` with entries at most `1/1000` (margin `4 - 3/1000 > 0`). This is the exact-arithmetic form:
the conclusion is `q(z) ≥ 0` for all *rational* `z`. -/
example (Δ : Matrix (Fin 3) (Fin 3) ℚ) (hΔsymm : Δ.IsSymm)
    (hΔ : ∀ i j, |Δ i j| ≤ 1 / 1000) :
    ((4 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) + Δ).PosSemidef := by
  have hmargin : ∀ z : Fin 3 → ℚ,
      (4 : ℚ) * ∑ i, z i ^ 2 ≤ quadForm ((4 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ)) z := by
    intro z
    rw [quadForm_smul, quadForm_one]
  refine posSemidef_add_of_margin (δ := 4) (ε := 1 / 1000) ?_ hmargin hΔsymm (by norm_num) hΔ ?_
  · simp [Matrix.IsSymm]
  · norm_num

end Instances

end LeafB.ErrProp

#print axioms LeafB.ErrProp.abs_quadForm_le_of_entry_le
#print axioms LeafB.ErrProp.abs_quadForm_le_of_entry_le_card
#print axioms LeafB.ErrProp.quadForm_add_perturb_ge
#print axioms LeafB.ErrProp.posSemidef_add_of_margin
#print axioms LeafB.ErrProp.abs_trace_mul_le
#print axioms LeafB.ErrProp.abs_sum_mul_sub_le
#print axioms LeafB.ErrProp.gap_budget
#print axioms LeafB.ErrProp.abs_sub_le_natCast_mul_of_steps
#print axioms LeafB.ErrProp.posSemidef_of_margin
#print axioms LeafB.ErrProp.posSemidef_of_entry_near
#print axioms LeafB.ErrProp.l1_sq_le_card_mul_l2sq
#print axioms LeafB.ErrProp.sq_entry_le_diag_mul
#print axioms LeafB.ErrProp.sum_abs_entry_le_card_mul_trace
#print axioms LeafB.ErrProp.abs_trace_mul_le_of_posSemidef
#print axioms LeafB.ErrProp.gap_budget_psd

open Matrix

/-- **The platform node**: entrywise perturbations of a quadratic form are bounded by
`ε · n · ∑ zᵢ²` (generic over any linear ordered field). -/
theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {n : ℕ} {Δ : Matrix (Fin n) (Fin n) R} {ε : R}
    (hε : 0 ≤ ε) (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    |z ⬝ᵥ (Δ *ᵥ z)| ≤ ε * (n : R) * ∑ i, z i ^ 2 := by
  simpa [LeafB.ErrProp.quadForm] using
    LeafB.ErrProp.abs_quadForm_le_of_entry_le_card (R := R) hε hΔ z
