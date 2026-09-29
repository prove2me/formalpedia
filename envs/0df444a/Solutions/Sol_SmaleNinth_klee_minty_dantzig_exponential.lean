-- Prove2me | solution 1 for SmaleNinth.klee_minty_dantzig_exponential
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T16:59:17.803802+00:00
-- url     : https://prove2.me/submissions/8aa39843-0e57-4816-abe5-c6b9cc14ae33

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_SimplexPivot
import Definitions.Def_SmaleNinth_KleeMinty
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Klee–Minty 1972: Dantzig's rule performs `2ⁿ − 1` pivots

Source: V. Klee, G.J. Minty, *How good is the simplex algorithm?*, Inequalities
III (1972), in the presentation of V. Chvátal, *Linear Programming*, Chapter 4.

Architecture. A vertex of the Klee–Minty cube is described by a pattern
`S : ℕ → Bool` recording, for each pair `i`, whether the original variable
`x_i` (`S i = true`) or the slack `s_i` (`S i = false`) is basic. Its
coordinates are `10^i · z S i` with `z S i = 10^i − 2 ∑_{j<i, S j} z S j`.
The basis matrix is unit lower triangular, so the pivot column and the dual
vector are obtained by explicit triangular solves; both are governed by the
sign sequence `sg S k = (−1)^{#{ℓ<k | S ℓ}}` through a telescoping identity.
The reduced cost of the nonbasic column of pair `i` is
`−10^{n−1−i} · sg S n · sg S i`, so Dantzig's rule enters the least pair `i`
with `sg S i = sg S n`, the ratio test expels the other member of the same
pair, and the new vertex is the pattern flipped at `i`. Along the binary
reflected Gray code `S_k i = bit_i(k) xor bit_{i+1}(k)` the improving pairs
at step `k` are exactly the zero bits of `k`, so step `k → k+1` flips the
least zero bit, and the run ends at `k = 2ⁿ − 1` with all reduced costs
nonnegative.
-/

/-!
Combinatorial layer for the Klee–Minty trajectory: the pattern `S : ℕ → Bool`
of basic original variables, the sign sequence `sg`, the vertex recursion
`T`/`z`, and the bits of `k + 1`.
-/

namespace SmaleNinth.KM

/-- Gray-code pattern of step `k`: `S k i = testBit k i xor testBit k (i+1)`. -/
def gray (k : ℕ) : ℕ → Bool := fun i => xor (k.testBit i) (k.testBit (i + 1))

/-- The sign sequence: `sg S k = (-1)^{#{ℓ < k | S ℓ}}`. -/
def sg (S : ℕ → Bool) : ℕ → ℝ
  | 0 => 1
  | k + 1 => if S k then -sg S k else sg S k

/-- Partial sums `T S i = ∑_{j < i, S j} z S j`, with `z S j = 10^j - 2 T S j`. -/
def T (S : ℕ → Bool) : ℕ → ℝ
  | 0 => 0
  | i + 1 => T S i + (if S i then (10 : ℝ) ^ i - 2 * T S i else 0)

/-- The scaled vertex coordinate of pair `i`: `z S i = 10^i - 2 T S i`. -/
def z (S : ℕ → Bool) (i : ℕ) : ℝ := (10 : ℝ) ^ i - 2 * T S i

@[simp] lemma sg_zero (S : ℕ → Bool) : sg S 0 = 1 := rfl
lemma sg_succ (S : ℕ → Bool) (k : ℕ) : sg S (k + 1) = if S k then -sg S k else sg S k := rfl
@[simp] lemma T_zero (S : ℕ → Bool) : T S 0 = 0 := rfl
lemma T_succ (S : ℕ → Bool) (i : ℕ) : T S (i + 1) = T S i + (if S i then z S i else 0) := rfl

lemma sg_sq (S : ℕ → Bool) (k : ℕ) : sg S k * sg S k = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sg_succ]; split_ifs <;> nlinarith [ih]

lemma sg_pm (S : ℕ → Bool) (k : ℕ) : sg S k = 1 ∨ sg S k = -1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sg_succ]; split_ifs <;> rcases ih with h | h <;> simp [h]

lemma abs_sg (S : ℕ → Bool) (k : ℕ) : |sg S k| = 1 := by
  rcases sg_pm S k with h | h <;> simp [h]

/-- Telescoping: `2 ∑_{a ≤ ℓ < k, S ℓ} sg ℓ = sg a - sg k`. -/
lemma two_mul_sum_sg (S : ℕ → Bool) (a k : ℕ) (hak : a ≤ k) :
    2 * ∑ ℓ ∈ Finset.Ico a k, (if S ℓ then sg S ℓ else 0) = sg S a - sg S k := by
  induction k, hak using Nat.le_induction with
  | base => simp
  | succ k hak ih =>
    rw [Finset.sum_Ico_succ_top hak, mul_add, ih, sg_succ]
    split_ifs <;> ring

/-- The sign of `sg` at `i` in terms of bits of `k` for the Gray pattern. -/
lemma sg_gray (k i : ℕ) :
    sg (gray k) i = if k.testBit 0 = k.testBit i then 1 else -1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sg_succ, ih]
    simp only [gray]
    rcases Bool.eq_false_or_eq_true (k.testBit 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (k.testBit i) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (k.testBit (i + 1)) with h2 | h2 <;> simp [h0, h1, h2]

/-- Bounds on the vertex recursion: `0 ≤ T i` and `9 T i ≤ 10^i - 1`. -/
lemma T_bounds (S : ℕ → Bool) (i : ℕ) : 0 ≤ T S i ∧ 9 * T S i ≤ (10 : ℝ) ^ i - 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨h0, h9⟩ := ih
    rw [T_succ, z]
    have hp : (0 : ℝ) < 10 ^ i := by positivity
    rw [pow_succ]
    split_ifs <;> constructor <;> nlinarith

lemma z_pos (S : ℕ → Bool) (i : ℕ) : 0 < z S i := by
  obtain ⟨h0, h9⟩ := T_bounds S i
  unfold z
  have hp : (0 : ℝ) < 10 ^ i := by positivity
  nlinarith

lemma z_le (S : ℕ → Bool) (i : ℕ) : z S i ≤ (10 : ℝ) ^ i := by
  obtain ⟨h0, _⟩ := T_bounds S i
  unfold z; linarith

lemma z_ge (S : ℕ → Bool) (i : ℕ) : (7 * (10 : ℝ) ^ i + 2) / 9 ≤ z S i := by
  obtain ⟨_, h9⟩ := T_bounds S i
  unfold z; linarith

/-- The ratio-test inequality: `2 z i ≤ z k` for `i < k`. -/
lemma two_z_le (S : ℕ → Bool) (i k : ℕ) (hik : i < k) : 2 * z S i ≤ z S k := by
  have h1 := z_le S i
  have h2 := z_ge S k
  have h3 : (10 : ℝ) ^ i * 10 ≤ 10 ^ k := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hik
  have h4 : (0 : ℝ) < 10 ^ k := by positivity
  linarith

/-- `T` and `z` at `k` depend only on `S` below `k`. -/
lemma T_congr (S S' : ℕ → Bool) (k : ℕ) (h : ∀ j < k, S j = S' j) : T S k = T S' k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [T_succ, T_succ, ih (fun j hj => h j (by omega)), h k (by omega)]
    unfold z
    rw [ih (fun j hj => h j (by omega))]

lemma z_congr (S S' : ℕ → Bool) (k : ℕ) (h : ∀ j < k, S j = S' j) : z S k = z S' k := by
  unfold z; rw [T_congr S S' k h]

/-- Flipping the pattern at `i`. -/
def flip (S : ℕ → Bool) (i : ℕ) : ℕ → Bool := fun j => if j = i then !S j else S j

lemma flip_apply_ne (S : ℕ → Bool) (i j : ℕ) (h : j ≠ i) : flip S i j = S j := by
  simp [flip, h]

lemma flip_apply_self (S : ℕ → Bool) (i : ℕ) : flip S i i = !S i := by
  simp [flip]

/-- The pivot identity: for `ℓ > i`, `T (flip S i) ℓ = T S ℓ + z S i * sg S ℓ * sg S i`. -/
lemma T_flip (S : ℕ → Bool) (i ℓ : ℕ) (hℓ : i < ℓ) :
    T (flip S i) ℓ = T S ℓ + z S i * sg S ℓ * sg S i := by
  induction ℓ, hℓ using Nat.le_induction with
  | base =>
    rw [T_succ, T_succ, T_congr (flip S i) S i (fun j hj => flip_apply_ne S i j (by omega)),
      z_congr (flip S i) S i (fun j hj => flip_apply_ne S i j (by omega)), flip_apply_self,
      sg_succ]
    have := sg_sq S i
    rcases Bool.eq_false_or_eq_true (S i) with h | h <;> rw [h] <;> simp
    · linear_combination (z S i) * this
    · linear_combination (-(z S i)) * this
  | succ ℓ hℓ ih =>
    have hz : z (flip S i) ℓ = z S ℓ - 2 * z S i * sg S ℓ * sg S i := by
      show (10 : ℝ) ^ ℓ - 2 * T (flip S i) ℓ = _
      rw [ih]; unfold z; ring
    rw [T_succ, T_succ, flip_apply_ne S i ℓ (by omega), sg_succ, hz, ih]
    rcases Bool.eq_false_or_eq_true (S ℓ) with h | h <;> rw [h] <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

lemma z_flip (S : ℕ → Bool) (i ℓ : ℕ) (hℓ : i < ℓ) :
    z (flip S i) ℓ = z S ℓ - 2 * z S i * sg S ℓ * sg S i := by
  unfold z; rw [T_flip S i ℓ hℓ, z]; ring

/-- Bits of `k + 1` when `k` has exactly `t` trailing ones. -/
lemma testBit_succ_of_trailing (t : ℕ) : ∀ k : ℕ, (∀ i < t, k.testBit i = true) →
    k.testBit t = false →
    ∀ i, (k + 1).testBit i = (if i < t then false else if i = t then true else k.testBit i) := by
  induction t with
  | zero =>
    intro k _ h0 i
    have hk : k % 2 = 0 := by simpa using h0
    cases i with
    | zero => simp; omega
    | succ i =>
      simp only [Nat.testBit_succ]
      have : (k + 1) / 2 = k / 2 := by omega
      simp [this]
  | succ t ih =>
    intro k hlow ht i
    have hk : k % 2 = 1 := by simpa using hlow 0 (by omega)
    have hdiv : (k + 1) / 2 = k / 2 + 1 := by omega
    have ih' := ih (k / 2) (fun i hi => by rw [← Nat.testBit_succ]; exact hlow (i + 1) (by omega))
      (by rw [← Nat.testBit_succ]; exact ht)
    cases i with
    | zero => simp; omega
    | succ i =>
      rw [Nat.testBit_succ, hdiv, ih' i, Nat.testBit_succ]
      by_cases h1 : i < t
      · simp [h1, show i + 1 < t + 1 by omega]
      · by_cases h2 : i = t
        · simp [h2]
        · simp [h1, h2, show ¬ (i + 1 < t + 1) by omega]

end SmaleNinth.KM

/-!
Matrix layer for the Klee–Minty trajectory: bases indexed by a Boolean
pattern, vertex points, the triangular basis matrix, and closed forms for
`B *ᵥ u`, `p ᵥ* B`, the pivot column and the dual vector.
-/

open Matrix LinearOptimization Finset

namespace SmaleNinth.KM

/-- ℕ-indexed entry of the `x`-column `i` of the Klee–Minty matrix at row `k`. -/
def colX (i k : ℕ) : ℝ := if i < k then 2 * (10 : ℝ) ^ (k - i) else if i = k then 1 else 0

/-- ℕ-indexed entry of the slack column `i` at row `k`. -/
def colS (i k : ℕ) : ℝ := if k = i then 1 else 0

lemma colX_of_lt {i k : ℕ} (h : k < i) : colX i k = 0 := by
  unfold colX; rw [if_neg (by omega), if_neg (by omega)]

lemma colX_self (i : ℕ) : colX i i = 1 := by simp [colX]

lemma colX_of_gt {i k : ℕ} (h : i < k) : colX i k = 2 * (10 : ℝ) ^ (k - i) := by
  simp [colX, h]

lemma colS_of_ne {i k : ℕ} (h : k ≠ i) : colS i k = 0 := by simp [colS, h]
lemma colS_self (i : ℕ) : colS i i = 1 := by simp [colS]

lemma kleeMintyA_x {n : ℕ} (k : Fin n) (i : ℕ) (hi : i < n) :
    kleeMintyA n k ⟨i, by omega⟩ = colX i k := by
  simp only [kleeMintyA, colX, hi, if_true]

lemma kleeMintyA_s {n : ℕ} (k : Fin n) (i : ℕ) (hi : i < n) :
    kleeMintyA n k ⟨n + i, by omega⟩ = colS i k := by
  simp only [kleeMintyA, colS]
  have : ¬ (n + i < n) := by omega
  simp only [this, if_false]
  by_cases h : (k : ℕ) = i
  · simp [h]
  · have h2 : ¬ (i = (k : ℕ)) := fun e => h e.symm
    simp [h, h2]

lemma kleeMintyc_x {n : ℕ} (i : ℕ) (hi : i < n) :
    kleeMintyc n ⟨i, by omega⟩ = -(10 : ℝ) ^ (n - 1 - i) := by
  simp [kleeMintyc, hi]

lemma kleeMintyc_s {n : ℕ} (i : ℕ) (hi : i < n) :
    kleeMintyc n ⟨n + i, by omega⟩ = 0 := by
  simp [kleeMintyc]

/-! ### Bases and points indexed by a pattern -/

/-- The basis of pattern `S`: pair `i` contributes `x_i` if `S i`, else `s_i`. -/
def basisOf (n : ℕ) (S : ℕ → Bool) : Fin n ↪ Fin (2 * n) :=
  ⟨fun i => if S i then ⟨i, by omega⟩ else ⟨n + i, by omega⟩, by
    intro a b hab
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val hab
    have e : ∀ c : Fin n,
        Fin.val (if S c then (⟨c, by omega⟩ : Fin (2 * n)) else (⟨n + c, by omega⟩ : Fin (2 * n)))
          = if S c then (c : ℕ) else n + c := fun c => by split_ifs <;> rfl
    rw [e a, e b] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)⟩

lemma basisOf_apply (n : ℕ) (S : ℕ → Bool) (i : Fin n) :
    basisOf n S i = if S i then ⟨i, by omega⟩ else ⟨n + i, by omega⟩ := rfl

lemma basisOf_val (n : ℕ) (S : ℕ → Bool) (i : Fin n) :
    ((basisOf n S i : Fin (2 * n)) : ℕ) = if S i then (i : ℕ) else n + i := by
  rw [basisOf_apply]; split_ifs <;> rfl

lemma basisOf_of_true (n : ℕ) (S : ℕ → Bool) (i : Fin n) (h : S i = true) :
    basisOf n S i = ⟨i, by omega⟩ := by rw [basisOf_apply, if_pos h]

lemma basisOf_of_false (n : ℕ) (S : ℕ → Bool) (i : Fin n) (h : S i = false) :
    basisOf n S i = ⟨n + i, by omega⟩ := by rw [basisOf_apply, if_neg (by simp [h])]

/-- The nonbasic column of pair `i`. -/
def nb (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) : Fin (2 * n) :=
  if S i then ⟨n + i, by omega⟩ else ⟨i, by omega⟩

lemma mem_range_basisOf (n : ℕ) (S : ℕ → Bool) (j : Fin (2 * n)) :
    j ∈ Set.range (basisOf n S) ↔
      (if (j : ℕ) < n then S j = true else S ((j : ℕ) - n) = false) := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [basisOf_val]
    by_cases h : S i = true
    · simp [h]
    · have h' : S i = false := by simpa using h
      simp [h']
  · intro h
    split_ifs at h with hj
    · exact ⟨⟨j, hj⟩, by rw [basisOf_apply]; simp [h]⟩
    · refine ⟨⟨(j : ℕ) - n, by omega⟩, ?_⟩
      rw [basisOf_apply]
      simp only [h, Bool.false_eq_true, if_false]
      exact Fin.ext (by simp; omega)

lemma nb_not_mem (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) :
    nb n S i hi ∉ Set.range (basisOf n S) := by
  rw [mem_range_basisOf]
  unfold nb
  by_cases h : S i = true
  · simp [h]
  · have h' : S i = false := by simpa using h
    simp [h', hi]

/-- The vertex of pattern `S`: pair `i` carries the value `10^i z S i` on its basic column. -/
noncomputable def pointOf (n : ℕ) (S : ℕ → Bool) : Fin (2 * n) → ℝ := fun j =>
  if (j : ℕ) < n then (if S j then (10 : ℝ) ^ (j : ℕ) * z S j else 0)
  else (if S ((j : ℕ) - n) then 0 else (10 : ℝ) ^ ((j : ℕ) - n) * z S ((j : ℕ) - n))

lemma pointOf_basic (n : ℕ) (S : ℕ → Bool) (i : Fin n) :
    pointOf n S (basisOf n S i) = (10 : ℝ) ^ (i : ℕ) * z S i := by
  unfold pointOf
  by_cases h : S i = true
  · rw [basisOf_of_true n S i h]; simp [h]
  · have h' : S i = false := by simpa using h
    rw [basisOf_of_false n S i h']
    have : ¬ (n + (i : ℕ) < n) := by omega
    simp [this, h']

lemma pointOf_nonbasic (n : ℕ) (S : ℕ → Bool) (j : Fin (2 * n))
    (hj : j ∉ Set.range (basisOf n S)) : pointOf n S j = 0 := by
  rw [mem_range_basisOf] at hj
  unfold pointOf
  split_ifs at hj with h1
  · simp [h1, hj]
  · simp [h1, hj]

lemma pointOf_nb (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) :
    pointOf n S (nb n S i hi) = 0 :=
  pointOf_nonbasic n S _ (nb_not_mem n S i hi)

/-! ### The basis matrix -/

lemma basisMatrix_apply (n : ℕ) (S : ℕ → Bool) (k ℓ : Fin n) :
    basisMatrix (kleeMintyA n) (basisOf n S) k ℓ =
      if S ℓ then colX ℓ k else colS ℓ k := by
  simp only [basisMatrix, submatrix_apply, id]
  by_cases h : S ℓ = true
  · rw [basisOf_of_true n S ℓ h, if_pos h]; exact kleeMintyA_x k ℓ ℓ.isLt
  · have h' : S ℓ = false := by simpa using h
    rw [basisOf_of_false n S ℓ h', if_neg h]; exact kleeMintyA_s k ℓ ℓ.isLt

lemma basisMatrix_isLowerTriangular (n : ℕ) (S : ℕ → Bool) :
    (basisMatrix (kleeMintyA n) (basisOf n S)).IsLowerTriangular := by
  intro k ℓ h
  have hkl : (k : ℕ) < ℓ := h
  rw [basisMatrix_apply]
  rw [colX_of_lt hkl, colS_of_ne (by omega)]
  simp

lemma basisMatrix_diag (n : ℕ) (S : ℕ → Bool) (k : Fin n) :
    basisMatrix (kleeMintyA n) (basisOf n S) k k = 1 := by
  rw [basisMatrix_apply, colX_self, colS_self]; simp

lemma basisMatrix_det (n : ℕ) (S : ℕ → Bool) :
    (basisMatrix (kleeMintyA n) (basisOf n S)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (basisMatrix_isLowerTriangular n S)]
  simp [basisMatrix_diag]

lemma basisMatrix_isUnit (n : ℕ) (S : ℕ → Bool) :
    IsUnit (basisMatrix (kleeMintyA n) (basisOf n S)) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [basisMatrix_det]; exact isUnit_one)

/-- The basis matrix is invertible. -/
noncomputable instance invertibleBasisMatrix (n : ℕ) (S : ℕ → Bool) :
    Invertible (basisMatrix (kleeMintyA n) (basisOf n S)) :=
  Matrix.invertibleOfIsUnitDet _ (by rw [basisMatrix_det]; exact isUnit_one)

lemma isStdBasis (n : ℕ) (S : ℕ → Bool) : IsStdBasis (kleeMintyA n) (basisOf n S) := by
  unfold IsStdBasis
  exact Matrix.linearIndependent_cols_iff_isUnit.mpr (basisMatrix_isUnit n S)

/-! ### Closed forms for `B *ᵥ u` and `p ᵥ* B` -/

lemma basisMatrix_mulVec (n : ℕ) (S : ℕ → Bool) (u : ℕ → ℝ) (k : Fin n) :
    (basisMatrix (kleeMintyA n) (basisOf n S) *ᵥ (fun i : Fin n => u i)) k
      = u k + 2 * ∑ ℓ ∈ range k, (if S ℓ then (10 : ℝ) ^ ((k : ℕ) - ℓ) * u ℓ else 0) := by
  simp only [Matrix.mulVec, dotProduct, basisMatrix_apply]
  rw [Fin.sum_univ_eq_sum_range (fun ℓ => (if S ℓ then colX ℓ k else colS ℓ k) * u ℓ) n]
  rw [← Finset.sum_range_add_sum_Ico _ (show (k : ℕ) + 1 ≤ n by omega), Finset.sum_range_succ]
  have h1 : ∑ ℓ ∈ Ico ((k : ℕ) + 1) n, (if S ℓ then colX ℓ k else colS ℓ k) * u ℓ = 0 := by
    apply Finset.sum_eq_zero
    intro ℓ hℓ
    rw [Finset.mem_Ico] at hℓ
    rw [colX_of_lt (by omega), colS_of_ne (by omega)]; simp
  have h2 : (if S k then colX k k else colS k k) * u k = u k := by
    rw [colX_self, colS_self]; simp
  have h3 : ∑ ℓ ∈ range k, (if S ℓ then colX ℓ k else colS ℓ k) * u ℓ
      = 2 * ∑ ℓ ∈ range k, (if S ℓ then (10 : ℝ) ^ ((k : ℕ) - ℓ) * u ℓ else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [Finset.mem_range] at hℓ
    rw [colX_of_gt hℓ, colS_of_ne (by omega)]
    split_ifs <;> ring
  rw [h1, h2, h3]; ring

lemma vecMul_basisMatrix (n : ℕ) (S : ℕ → Bool) (p : ℕ → ℝ) (ℓ : Fin n) :
    ((fun i : Fin n => p i) ᵥ* basisMatrix (kleeMintyA n) (basisOf n S)) ℓ
      = if S ℓ then p ℓ + 2 * ∑ k ∈ Ico ((ℓ : ℕ) + 1) n, (10 : ℝ) ^ (k - ℓ) * p k
        else p ℓ := by
  simp only [Matrix.vecMul, dotProduct, basisMatrix_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => p k * (if S ℓ then colX ℓ k else colS ℓ k)) n]
  by_cases h : S ℓ = true
  · simp only [h, if_true]
    rw [← Finset.sum_range_add_sum_Ico _ (show (ℓ : ℕ) + 1 ≤ n by omega),
      Finset.sum_range_succ]
    have h1 : ∑ k ∈ range ℓ, p k * colX ℓ k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      rw [colX_of_lt hk]; simp
    have h3 : ∑ k ∈ Ico ((ℓ : ℕ) + 1) n, p k * colX ℓ k
        = 2 * ∑ k ∈ Ico ((ℓ : ℕ) + 1) n, (10 : ℝ) ^ (k - ℓ) * p k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [colX_of_gt (by omega)]; ring
    rw [h1, h3, colX_self]; ring
  · have h' : S ℓ = false := by simpa using h
    simp only [h', Bool.false_eq_true, if_false]
    have : ∀ k ∈ range n, p k * colS ℓ k = if k = (ℓ : ℕ) then p k else 0 := by
      intro k _
      unfold colS; split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp [ℓ.isLt]

/-! ### The pivot column and the dual vector -/

/-- The pivot column `u = B⁻¹ A_j` for the nonbasic column of pair `i`, ℕ-indexed. -/
noncomputable def pv (S : ℕ → Bool) (i : ℕ) : ℕ → ℝ := fun k =>
  if k < i then 0 else if k = i then 1 else (10 : ℝ) ^ (k - i) * (2 * sg S k * sg S i)

/-- The dual vector `p = c_B B⁻¹`, ℕ-indexed. -/
noncomputable def dv (S : ℕ → Bool) (n : ℕ) : ℕ → ℝ := fun k =>
  if S k then -((10 : ℝ) ^ (n - 1 - k)) * sg S n * sg S (k + 1) else 0

lemma pow_sub_mul_pow_sub {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    (10 : ℝ) ^ (c - b) * 10 ^ (b - a) = 10 ^ (c - a) := by
  rw [← pow_add]; congr 1; omega

lemma sum_Ico_sg_succ (S : ℕ → Bool) (a b : ℕ) :
    ∑ k ∈ Ico a b, (if S k then sg S (k + 1) else 0)
      = -∑ k ∈ Ico a b, (if S k then sg S k else 0) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sg_succ]
  split_ifs <;> simp

/-- `B *ᵥ pv = A_j` for the nonbasic column `j` of pair `i`. -/
lemma basisMatrix_mulVec_pv (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) :
    basisMatrix (kleeMintyA n) (basisOf n S) *ᵥ (fun k : Fin n => pv S i k)
      = fun k => kleeMintyA n k (nb n S i hi) := by
  funext k
  rw [basisMatrix_mulVec]
  have hcol : kleeMintyA n k (nb n S i hi) = if S i then colS i k else colX i k := by
    unfold nb
    by_cases h : S i = true
    · rw [if_pos h, if_pos h]; exact kleeMintyA_s k i hi
    · rw [if_neg h, if_neg h]; exact kleeMintyA_x k i hi
  rw [hcol]
  rcases lt_trichotomy (k : ℕ) i with hk | hk | hk
  · -- k < i
    have hpv : pv S i k = 0 := by simp [pv, hk]
    have hsum : ∑ ℓ ∈ range k, (if S ℓ then (10 : ℝ) ^ ((k : ℕ) - ℓ) * pv S i ℓ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      rw [Finset.mem_range] at hℓ
      have : pv S i ℓ = 0 := by simp [pv, show ℓ < i by omega]
      simp [this]
    rw [hpv, hsum, colS_of_ne (by omega), colX_of_lt hk]; simp
  · -- k = i
    have hpv : pv S i k = 1 := by simp [pv, hk]
    have hsum : ∑ ℓ ∈ range k, (if S ℓ then (10 : ℝ) ^ ((k : ℕ) - ℓ) * pv S i ℓ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      rw [Finset.mem_range] at hℓ
      have : pv S i ℓ = 0 := by simp [pv, show ℓ < i by omega]
      simp [this]
    rw [hpv, hsum, hk, colS_self, colX_self]; simp
  · -- k > i
    have hpv : pv S i k = (10 : ℝ) ^ ((k : ℕ) - i) * (2 * sg S k * sg S i) := by
      simp [pv, show ¬ ((k : ℕ) < i) by omega, show (k : ℕ) ≠ i by omega]
    rw [hpv]
    rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ (k : ℕ) by omega),
      Finset.sum_eq_sum_Ico_succ_bot hk]
    have h1 : ∑ ℓ ∈ range i, (if S ℓ then (10 : ℝ) ^ ((k : ℕ) - ℓ) * pv S i ℓ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      rw [Finset.mem_range] at hℓ
      have : pv S i ℓ = 0 := by simp [pv, hℓ]
      simp [this]
    have h2 : pv S i i = 1 := by simp [pv]
    have h3 : ∑ ℓ ∈ Ico (i + 1) k, (if S ℓ then (10 : ℝ) ^ ((k : ℕ) - ℓ) * pv S i ℓ else 0)
        = (10 : ℝ) ^ ((k : ℕ) - i) * (2 * sg S i) *
            ∑ ℓ ∈ Ico (i + 1) k, (if S ℓ then sg S ℓ else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      rw [Finset.mem_Ico] at hℓ
      have : pv S i ℓ = (10 : ℝ) ^ (ℓ - i) * (2 * sg S ℓ * sg S i) := by
        simp [pv, show ¬ (ℓ < i) by omega, show ℓ ≠ i by omega]
      rw [this]
      split_ifs
      · rw [← mul_assoc ((10 : ℝ) ^ ((k : ℕ) - ℓ)), pow_sub_mul_pow_sub (by omega) (by omega)]
        ring
      · simp
    rw [h1, h2, h3]
    have htel := two_mul_sum_sg S (i + 1) k (by omega)
    have hsq := sg_sq S i
    rw [sg_succ] at htel
    by_cases h : S i = true
    · rw [colS_of_ne (by omega)]
      simp only [h, if_true] at htel ⊢
      linear_combination (2 * (10 : ℝ) ^ ((k : ℕ) - i) * sg S i) * htel
        - (2 * (10 : ℝ) ^ ((k : ℕ) - i)) * hsq
    · have h' : S i = false := by simpa using h
      rw [colX_of_gt hk]
      simp only [h', Bool.false_eq_true, if_false] at htel ⊢
      linear_combination (2 * (10 : ℝ) ^ ((k : ℕ) - i) * sg S i) * htel
        + (2 * (10 : ℝ) ^ ((k : ℕ) - i)) * hsq

/-- `dv ᵥ* B = c_B`. -/
lemma vecMul_dv (n : ℕ) (S : ℕ → Bool) :
    (fun k : Fin n => dv S n k) ᵥ* basisMatrix (kleeMintyA n) (basisOf n S)
      = fun ℓ => kleeMintyc n (basisOf n S ℓ) := by
  funext ℓ
  rw [vecMul_basisMatrix]
  by_cases h : S ℓ = true
  · rw [if_pos h, basisOf_of_true n S ℓ h, kleeMintyc_x ℓ ℓ.isLt]
    have h1 : ∑ k ∈ Ico ((ℓ : ℕ) + 1) n, (10 : ℝ) ^ (k - ℓ) * dv S n k
        = -((10 : ℝ) ^ (n - 1 - ℓ) * sg S n) *
            ∑ k ∈ Ico ((ℓ : ℕ) + 1) n, (if S k then sg S (k + 1) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      unfold dv
      split_ifs
      · rw [show (10 : ℝ) ^ (k - ℓ) * (-(10 : ℝ) ^ (n - 1 - k) * sg S n * sg S (k + 1))
            = -((10 : ℝ) ^ (n - 1 - k) * 10 ^ (k - ℓ)) * sg S n * sg S (k + 1) by ring,
          pow_sub_mul_pow_sub (by omega) (by omega)]
        ring
      · simp
    rw [h1, sum_Ico_sg_succ]
    have htel := two_mul_sum_sg S ((ℓ : ℕ) + 1) n (by omega)
    have hsq := sg_sq S n
    have hdv : dv S n ℓ = -((10 : ℝ) ^ (n - 1 - ℓ)) * sg S n * sg S (ℓ + 1) := by
      simp [dv, h]
    rw [hdv]
    linear_combination ((10 : ℝ) ^ (n - 1 - ℓ) * sg S n) * htel
      - (10 : ℝ) ^ (n - 1 - ℓ) * hsq
  · have h' : S ℓ = false := by simpa using h
    rw [if_neg h, basisOf_of_false n S ℓ h', kleeMintyc_s ℓ ℓ.isLt]
    simp [dv, h']

/-! ### Solve lemmas for the simplex quantities -/

lemma pivotColumn_eq_of_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n)
    (j : Fin n) [Invertible (basisMatrix A B)] (u : Fin m → ℝ)
    (h : basisMatrix A B *ᵥ u = fun i => A i j) : pivotColumn A B j = u := by
  unfold pivotColumn
  rw [← h, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

lemma reducedCost_eq_of_vecMul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) [Invertible (basisMatrix A B)] (p : Fin m → ℝ)
    (h : p ᵥ* basisMatrix A B = fun i => c (B i)) :
    reducedCost A c B j = c j - p ⬝ᵥ (fun i => A i j) := by
  unfold reducedCost
  rw [← h, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_inv_of_invertible,
    Matrix.vecMul_one]

lemma pivotColumn_nb (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) :
    pivotColumn (kleeMintyA n) (basisOf n S) (nb n S i hi) = fun k : Fin n => pv S i k := by
  exact pivotColumn_eq_of_mulVec _ _ _ _ (basisMatrix_mulVec_pv n S i hi)

/-- The reduced cost of the nonbasic column of pair `i`. -/
lemma reducedCost_nb (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) :
    reducedCost (kleeMintyA n) (kleeMintyc n) (basisOf n S) (nb n S i hi)
      = -((10 : ℝ) ^ (n - 1 - i)) * sg S n * sg S i := by
  rw [reducedCost_eq_of_vecMul _ _ _ _ _ (vecMul_dv n S)]
  simp only [dotProduct]
  by_cases h : S i = true
  · have hnb : nb n S i hi = ⟨n + i, by omega⟩ := by simp [nb, h]
    have hc : kleeMintyc n (nb n S i hi) = 0 := by rw [hnb]; exact kleeMintyc_s i hi
    have hA : ∀ k : Fin n, kleeMintyA n k (nb n S i hi) = colS i k := fun k => by
      rw [hnb]; exact kleeMintyA_s k i hi
    have hsum : ∑ k : Fin n, dv S n k * kleeMintyA n k (nb n S i hi)
        = ∑ k : Fin n, dv S n k * colS i k :=
      Finset.sum_congr rfl (fun k _ => by rw [hA k])
    rw [hc, hsum]
    rw [Fin.sum_univ_eq_sum_range (fun k => dv S n k * colS i k) n]
    have : ∀ k ∈ range n, dv S n k * colS i k = if k = i then dv S n k else 0 := by
      intro k _; unfold colS; split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp only [Finset.mem_range, hi, if_true]
    have hdv : dv S n i = -((10 : ℝ) ^ (n - 1 - i)) * sg S n * sg S (i + 1) := by simp [dv, h]
    rw [hdv, sg_succ, if_pos h]; ring
  · have h' : S i = false := by simpa using h
    have hnb : nb n S i hi = ⟨i, by omega⟩ := by simp [nb, h']
    have hc : kleeMintyc n (nb n S i hi) = -(10 : ℝ) ^ (n - 1 - i) := by
      rw [hnb]; exact kleeMintyc_x i hi
    have hA : ∀ k : Fin n, kleeMintyA n k (nb n S i hi) = colX i k := fun k => by
      rw [hnb]; exact kleeMintyA_x k i hi
    have hsum : ∑ k : Fin n, dv S n k * kleeMintyA n k (nb n S i hi)
        = ∑ k : Fin n, dv S n k * colX i k :=
      Finset.sum_congr rfl (fun k _ => by rw [hA k])
    rw [hc, hsum]
    rw [Fin.sum_univ_eq_sum_range (fun k => dv S n k * colX i k) n]
    rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ n by omega),
      Finset.sum_eq_sum_Ico_succ_bot hi]
    have h1 : ∑ k ∈ range i, dv S n k * colX i k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      rw [colX_of_lt hk]; simp
    have h2 : dv S n i = 0 := by simp [dv, h']
    have h3 : ∑ k ∈ Ico (i + 1) n, dv S n k * colX i k
        = -(2 * (10 : ℝ) ^ (n - 1 - i) * sg S n) *
            ∑ k ∈ Ico (i + 1) n, (if S k then sg S (k + 1) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [colX_of_gt (by omega)]
      unfold dv
      split_ifs
      · rw [show -(10 : ℝ) ^ (n - 1 - k) * sg S n * sg S (k + 1) * (2 * 10 ^ (k - i))
            = -((10 : ℝ) ^ (n - 1 - k) * 10 ^ (k - i)) * sg S n * sg S (k + 1) * 2 by ring,
          pow_sub_mul_pow_sub (by omega) (by omega)]
        ring
      · simp
    rw [h1, h2, h3, sum_Ico_sg_succ]
    have htel := two_mul_sum_sg S (i + 1) n (by omega)
    have hsq := sg_sq S n
    rw [sg_succ, if_neg h] at htel
    linear_combination (-((10 : ℝ) ^ (n - 1 - i) * sg S n)) * htel
      + (10 : ℝ) ^ (n - 1 - i) * hsq

end SmaleNinth.KM

/-!
Pivot layer for the Klee–Minty trajectory: every pattern vertex is a simplex
state, flipping the least improving pair is a Dantzig pivot, and a pattern
with no improving pair is optimal-terminal.
-/

open Matrix LinearOptimization Finset

namespace SmaleNinth.KM

/-! ### Pair index of a column -/

/-- The pair index of a column of the Klee–Minty matrix. -/
def pairIdx (n : ℕ) (q : Fin (2 * n)) : ℕ := if (q : ℕ) < n then (q : ℕ) else (q : ℕ) - n

lemma pairIdx_lt (n : ℕ) (q : Fin (2 * n)) : pairIdx n q < n := by
  unfold pairIdx; have := q.isLt; split_ifs <;> omega

lemma pairIdx_basisOf (n : ℕ) (S : ℕ → Bool) (i : Fin n) : pairIdx n (basisOf n S i) = i := by
  unfold pairIdx; rw [basisOf_val]; split_ifs <;> omega

lemma pairIdx_nb (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) : pairIdx n (nb n S i hi) = i := by
  unfold pairIdx nb; split_ifs <;> simp_all <;> omega

lemma basisOf_pairIdx (n : ℕ) (S : ℕ → Bool) (q : Fin (2 * n))
    (hq : q ∈ Set.range (basisOf n S)) : basisOf n S ⟨pairIdx n q, pairIdx_lt n q⟩ = q := by
  obtain ⟨i, rfl⟩ := hq
  congr 1
  exact Fin.ext (pairIdx_basisOf n S i)

lemma nb_of_not_mem (n : ℕ) (S : ℕ → Bool) (q : Fin (2 * n))
    (hq : q ∉ Set.range (basisOf n S)) : q = nb n S (pairIdx n q) (pairIdx_lt n q) := by
  rw [mem_range_basisOf] at hq
  unfold nb pairIdx
  split_ifs at hq with h1 <;> simp only [h1, if_true, if_false]
  · have h' : S q = false := by simpa using hq
    simp [h']
  · have h' : S ((q : ℕ) - n) = true := by simpa using hq
    simp only [h', if_true]
    exact Fin.ext (by simp; omega)

lemma eq_nb_iff (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) (q : Fin (2 * n)) :
    q = nb n S i hi ↔ (pairIdx n q = i ∧ q ∉ Set.range (basisOf n S)) := by
  constructor
  · rintro rfl; exact ⟨pairIdx_nb n S i hi, nb_not_mem n S i hi⟩
  · rintro ⟨h1, h2⟩
    have := nb_of_not_mem n S q h2
    rw [this]; congr 1

/-- Membership in the range of the flipped basis. -/
lemma mem_range_flip (n : ℕ) (S : ℕ → Bool) (i : ℕ) (q : Fin (2 * n)) :
    q ∈ Set.range (basisOf n (flip S i)) ↔
      (if pairIdx n q = i then q ∉ Set.range (basisOf n S) else q ∈ Set.range (basisOf n S)) := by
  rw [mem_range_basisOf, mem_range_basisOf]
  unfold pairIdx
  by_cases hq : (q : ℕ) < n
  · simp only [hq, if_true]
    by_cases h : (q : ℕ) = i
    · subst h; simp [flip_apply_self]
    · simp [h, flip_apply_ne S i _ h]
  · simp only [hq, if_false]
    by_cases h : (q : ℕ) - n = i
    · rw [h, if_pos rfl, flip_apply_self]; simp
    · simp [h, flip_apply_ne S i _ h]

/-- The point in terms of the pair index. -/
lemma pointOf_eq (n : ℕ) (S : ℕ → Bool) (q : Fin (2 * n)) :
    pointOf n S q = if q ∈ Set.range (basisOf n S)
      then (10 : ℝ) ^ (pairIdx n q) * z S (pairIdx n q) else 0 := by
  split_ifs with h
  · conv_lhs => rw [← basisOf_pairIdx n S q h]
    rw [pointOf_basic]
  · exact pointOf_nonbasic n S q h

/-! ### Every pattern vertex is a simplex state -/

lemma T_eq_sum (S : ℕ → Bool) (k : ℕ) :
    T S k = ∑ j ∈ range k, (if S j then z S j else 0) := by
  induction k with
  | zero => simp
  | succ k ih => rw [T_succ, Finset.sum_range_succ, ih]

/-- ℕ-indexed value of `pointOf` at column `j`. -/
noncomputable def pval (n : ℕ) (S : ℕ → Bool) (j : ℕ) : ℝ :=
  if j < n then (if S j then (10 : ℝ) ^ j * z S j else 0)
  else (if S (j - n) then 0 else (10 : ℝ) ^ (j - n) * z S (j - n))

lemma pointOf_eq_pval (n : ℕ) (S : ℕ → Bool) (j : Fin (2 * n)) : pointOf n S j = pval n S j := rfl

/-- ℕ-indexed entry of the Klee–Minty matrix at row `k`, column `j`. -/
noncomputable def aval (n : ℕ) (k j : ℕ) : ℝ := if j < n then colX j k else colS (j - n) k

lemma kleeMintyA_eq_aval (n : ℕ) (k : Fin n) (j : Fin (2 * n)) :
    kleeMintyA n k j = aval n k j := by
  unfold aval
  by_cases h : (j : ℕ) < n
  · rw [if_pos h]
    have : j = ⟨(j : ℕ), by omega⟩ := Fin.ext rfl
    rw [this]; exact kleeMintyA_x k j h
  · rw [if_neg h]
    have hj : j = ⟨n + ((j : ℕ) - n), by omega⟩ := Fin.ext (by simp; omega)
    have hlt : (j : ℕ) - n < n := by have := j.isLt; omega
    have := kleeMintyA_s k ((j : ℕ) - n) hlt
    conv_lhs => rw [hj]
    exact this

lemma mulVec_pointOf (n : ℕ) (S : ℕ → Bool) (k : Fin n) :
    (kleeMintyA n *ᵥ pointOf n S) k = (100 : ℝ) ^ (k : ℕ) := by
  simp only [Matrix.mulVec, dotProduct, kleeMintyA_eq_aval, pointOf_eq_pval]
  rw [Fin.sum_univ_eq_sum_range (fun j => aval n k j * pval n S j) (2 * n), two_mul,
    Finset.sum_range_add]
  have hX : ∑ j ∈ range n, aval n k j * pval n S j
      = 2 * (10 : ℝ) ^ (k : ℕ) * T S k + (if S k then (10 : ℝ) ^ (k : ℕ) * z S k else 0) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show (k : ℕ) + 1 ≤ n by omega),
      Finset.sum_range_succ]
    have h1 : ∑ j ∈ Ico ((k : ℕ) + 1) n, aval n k j * pval n S j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ico] at hj
      unfold aval; rw [if_pos (by omega), colX_of_lt (by omega)]; simp
    have h2 : aval n k k * pval n S k = (if S k then (10 : ℝ) ^ (k : ℕ) * z S k else 0) := by
      unfold aval pval; rw [if_pos k.isLt, if_pos k.isLt, colX_self]; simp
    have h3 : ∑ j ∈ range k, aval n k j * pval n S j = 2 * (10 : ℝ) ^ (k : ℕ) * T S k := by
      rw [T_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      unfold aval pval
      rw [if_pos (by omega), if_pos (by omega), colX_of_gt hj]
      split_ifs
      · rw [show (10 : ℝ) ^ (k : ℕ) = 10 ^ ((k : ℕ) - j) * 10 ^ j by
          rw [← pow_add]; congr 1; omega]
        ring
      · simp
    rw [h1, h2, h3]; ring
  have hS : ∑ j ∈ range n, aval n k (n + j) * pval n S (n + j)
      = (if S k then 0 else (10 : ℝ) ^ (k : ℕ) * z S k) := by
    have : ∀ j ∈ range n, aval n k (n + j) * pval n S (n + j)
        = if j = (k : ℕ) then (if S k then 0 else (10 : ℝ) ^ (k : ℕ) * z S k) else 0 := by
      intro j _
      unfold aval pval
      rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
      unfold colS
      by_cases h : j = (k : ℕ)
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h]; simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp [k.isLt]
  rw [hX, hS]
  have hz : z S k = (10 : ℝ) ^ (k : ℕ) - 2 * T S k := rfl
  have h100 : (100 : ℝ) ^ (k : ℕ) = 10 ^ (k : ℕ) * 10 ^ (k : ℕ) := by
    rw [← mul_pow]; norm_num
  rw [h100]
  split_ifs <;> rw [hz] <;> ring

lemma pointOf_nonneg (n : ℕ) (S : ℕ → Bool) : 0 ≤ pointOf n S := by
  intro q
  rw [pointOf_eq]
  split_ifs
  · have := z_pos S (pairIdx n q); positivity
  · exact le_rfl

lemma isSimplexState (n : ℕ) (S : ℕ → Bool) :
    IsSimplexState (kleeMintyA n) (kleeMintyb n) (basisOf n S) (pointOf n S) := by
  refine ⟨isStdBasis n S, ⟨?_, pointOf_nonneg n S⟩, fun j hj => pointOf_nonbasic n S j hj⟩
  funext k
  rw [mulVec_pointOf]; rfl

/-! ### Sign helpers -/

lemma sg_mul_sg_eq_one_iff (S : ℕ → Bool) (a b : ℕ) :
    sg S a * sg S b = 1 ↔ sg S a = sg S b := by
  rcases sg_pm S a with ha | ha <;> rcases sg_pm S b with hb | hb <;> simp [ha, hb] <;> norm_num

lemma sg_mul_sg_eq_neg_one_of_ne (S : ℕ → Bool) (a b : ℕ) (h : sg S a ≠ sg S b) :
    sg S a * sg S b = -1 := by
  rcases sg_pm S a with ha | ha <;> rcases sg_pm S b with hb | hb <;> simp_all <;> norm_num

lemma sg_mul_sg_le (S : ℕ → Bool) (a b : ℕ) : sg S a * sg S b ≤ 1 := by
  rcases sg_pm S a with ha | ha <;> rcases sg_pm S b with hb | hb <;> simp [ha, hb]

/-! ### The basic direction on the Klee–Minty basis -/

lemma sum_single_basisOf (n : ℕ) (S : ℕ → Bool) (v : Fin n → ℝ) (q : Fin (2 * n)) :
    (∑ i : Fin n, Pi.single (basisOf n S i) (v i) : Fin (2 * n) → ℝ) q
      = if h : q ∈ Set.range (basisOf n S) then v ⟨pairIdx n q, pairIdx_lt n q⟩ else 0 := by
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem ⟨pairIdx n q, pairIdx_lt n q⟩ (Finset.mem_univ _)]
    · rw [if_pos (basisOf_pairIdx n S q h).symm]
    · intro i _ hi
      rw [if_neg]
      intro hq
      apply hi
      apply (basisOf n S).injective
      rw [basisOf_pairIdx n S q h, hq]
  · apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro hq
    exact h ⟨i, hq.symm⟩

lemma basicDirection_apply (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) (q : Fin (2 * n)) :
    basicDirection (kleeMintyA n) (basisOf n S) (nb n S i hi) q
      = (if q = nb n S i hi then 1 else 0)
        - (if q ∈ Set.range (basisOf n S) then pv S i (pairIdx n q) else 0) := by
  unfold basicDirection
  rw [Pi.sub_apply, Pi.single_apply]
  have hpc : (basisMatrix (kleeMintyA n) (basisOf n S))⁻¹.mulVec
      (fun i' => kleeMintyA n i' (nb n S i hi)) = fun k : Fin n => pv S i k :=
    pivotColumn_nb n S i hi
  rw [hpc, sum_single_basisOf]
  by_cases hq : q ∈ Set.range (basisOf n S)
  · rw [dif_pos hq, if_pos hq]
  · rw [dif_neg hq, if_neg hq]

/-! ### The Dantzig pivot -/

lemma pointOf_flip_eq (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) :
    pointOf n (flip S i) = pointOf n S +
      (pointOf n S (basisOf n S ⟨i, hi⟩) /
        pivotColumn (kleeMintyA n) (basisOf n S) (nb n S i hi) ⟨i, hi⟩) •
        basicDirection (kleeMintyA n) (basisOf n S) (nb n S i hi) := by
  funext q
  rw [pivotColumn_nb, pointOf_basic, Pi.add_apply, Pi.smul_apply, basicDirection_apply,
    smul_eq_mul]
  have hpvi : pv S i i = 1 := by simp [pv]
  simp only [hpvi, div_one]
  rw [pointOf_eq n (flip S i) q, pointOf_eq n S q]
  have hflip := mem_range_flip n S i q
  have hz_lo : ∀ j ≤ i, z (flip S i) j = z S j := fun j hj =>
    z_congr _ _ j (fun j' hj' => flip_apply_ne S i j' (by omega))
  by_cases hpi : pairIdx n q = i
  · rw [if_pos hpi] at hflip
    by_cases hq : q ∈ Set.range (basisOf n S)
    · -- the leaving column
      have hq' : q ∉ Set.range (basisOf n (flip S i)) := fun h => (hflip.mp h) hq
      have hnq : ¬ q = nb n S i hi := by rw [eq_nb_iff]; tauto
      simp only [if_neg hq', if_pos hq, if_neg hnq, hpi, hpvi]
      ring
    · -- the entering column
      have hq' : q ∈ Set.range (basisOf n (flip S i)) := hflip.mpr hq
      have hnq : q = nb n S i hi := (eq_nb_iff n S i hi q).mpr ⟨hpi, hq⟩
      simp only [if_pos hq', if_neg hq, if_pos hnq, hpi, hz_lo i le_rfl]
      ring
  · rw [if_neg hpi] at hflip
    have hnq : ¬ q = nb n S i hi := by rw [eq_nb_iff]; tauto
    by_cases hq : q ∈ Set.range (basisOf n S)
    · simp only [if_pos (hflip.mpr hq), if_pos hq, if_neg hnq]
      rcases lt_or_gt_of_ne hpi with hlt | hgt
      · rw [hz_lo _ hlt.le]
        have : pv S i (pairIdx n q) = 0 := by simp [pv, hlt]
        rw [this]; ring
      · rw [z_flip S i _ hgt]
        have : pv S i (pairIdx n q) = (10 : ℝ) ^ (pairIdx n q - i) *
            (2 * sg S (pairIdx n q) * sg S i) := by
          simp [pv, show ¬ (pairIdx n q < i) by omega, show pairIdx n q ≠ i by omega]
        rw [this, show (10 : ℝ) ^ (pairIdx n q) = 10 ^ i * 10 ^ (pairIdx n q - i) by
          rw [← pow_add]; congr 1; omega]
        ring
    · simp only [if_neg (fun h => hq (hflip.mp h)), if_neg hq, if_neg hnq]; ring

lemma ratio_test (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n) (i' : Fin n)
    (hpos : 0 < pivotColumn (kleeMintyA n) (basisOf n S) (nb n S i hi) i') :
    pointOf n S (basisOf n S ⟨i, hi⟩) /
        pivotColumn (kleeMintyA n) (basisOf n S) (nb n S i hi) ⟨i, hi⟩
      ≤ pointOf n S (basisOf n S i') /
        pivotColumn (kleeMintyA n) (basisOf n S) (nb n S i hi) i' := by
  rw [pivotColumn_nb] at hpos ⊢
  rw [pointOf_basic, pointOf_basic]
  dsimp only at hpos ⊢
  have hpvi : pv S i i = 1 := by simp [pv]
  rw [hpvi, div_one]
  rcases lt_trichotomy (i' : ℕ) i with hlt | heq | hgt
  · exfalso; simp [pv, hlt] at hpos
  · rw [heq, hpvi, div_one]
  · have hform : pv S i i' = (10 : ℝ) ^ ((i' : ℕ) - i) * (2 * sg S i' * sg S i) := by
      simp [pv, show ¬ ((i' : ℕ) < i) by omega, show (i' : ℕ) ≠ i by omega]
    rw [hform] at hpos ⊢
    have hsg : sg S i' * sg S i = 1 := by
      rcases sg_pm S i' with h1 | h1 <;> rcases sg_pm S i with h2 | h2 <;>
        simp [h1, h2] at hpos ⊢ <;> nlinarith [pow_pos (show (0 : ℝ) < 10 by norm_num) ((i' : ℕ) - i)]
    have h2 : 2 * sg S i' * sg S i = 2 := by rw [mul_assoc, hsg, mul_one]
    rw [h2] at hpos ⊢
    rw [le_div_iff₀ hpos]
    have hpow : (10 : ℝ) ^ (i' : ℕ) = 10 ^ i * 10 ^ ((i' : ℕ) - i) := by
      rw [← pow_add]; congr 1; omega
    have hzz := two_z_le S i i' hgt
    have hp : (0 : ℝ) < 10 ^ ((i' : ℕ) - i) := by positivity
    have hp' : (0 : ℝ) < 10 ^ i := by positivity
    rw [hpow]
    nlinarith [mul_pos hp hp']

lemma reducedCost_le (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n)
    (hmin : ∀ p < i, sg S p ≠ sg S n) (hieq : sg S i = sg S n) (j' : Fin (2 * n)) :
    reducedCost (kleeMintyA n) (kleeMintyc n) (basisOf n S) (nb n S i hi)
      ≤ reducedCost (kleeMintyA n) (kleeMintyc n) (basisOf n S) j' := by
  rw [reducedCost_nb]
  have hprod : sg S n * sg S i = 1 := by rw [mul_comm, sg_mul_sg_eq_one_iff]; exact hieq
  rw [mul_assoc, hprod, mul_one]
  by_cases hj : j' ∈ Set.range (basisOf n S)
  · obtain ⟨i', rfl⟩ := hj
    rw [reducedCost_basic]
    have : (0 : ℝ) < 10 ^ (n - 1 - i) := by positivity
    linarith
  · rw [nb_of_not_mem n S j' hj, reducedCost_nb]
    set p := pairIdx n j' with hp
    have hpn := pairIdx_lt n j'
    rcases lt_or_ge p i with hlt | hge
    · have : sg S n * sg S p = -1 := by
        rw [mul_comm]; exact sg_mul_sg_eq_neg_one_of_ne S p n (hmin p hlt)
      rw [mul_assoc, this]
      have h1 : (0 : ℝ) < 10 ^ (n - 1 - i) := by positivity
      have h2 : (0 : ℝ) < 10 ^ (n - 1 - p) := by positivity
      linarith
    · have h1 := sg_mul_sg_le S n p
      have h2 : (10 : ℝ) ^ (n - 1 - p) ≤ 10 ^ (n - 1 - i) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (0 : ℝ) < 10 ^ (n - 1 - p) := by positivity
      rw [mul_assoc]
      nlinarith

/-- Flipping the least improving pair is a Dantzig pivot. -/
lemma isDantzigPivot (n : ℕ) (S : ℕ → Bool) (i : ℕ) (hi : i < n)
    (hmin : ∀ p < i, sg S p ≠ sg S n) (hieq : sg S i = sg S n) :
    IsDantzigPivot (kleeMintyA n) (kleeMintyc n) (basisOf n S) (pointOf n S)
      (basisOf n (flip S i)) (pointOf n (flip S i)) := by
  refine ⟨nb n S i hi, ⟨i, hi⟩, ⟨nb_not_mem n S i hi, ?_, ?_, ?_, ?_, pointOf_flip_eq n S i hi⟩,
    fun i' hpos => ratio_test n S i hi i' hpos, reducedCost_le n S i hi hmin hieq⟩
  · rw [reducedCost_nb]
    have hprod : sg S n * sg S i = 1 := by rw [mul_comm, sg_mul_sg_eq_one_iff]; exact hieq
    rw [mul_assoc, hprod, mul_one]
    have : (0 : ℝ) < 10 ^ (n - 1 - i) := by positivity
    linarith
  · rw [pivotColumn_nb]; simp [pv]
  · intro i' hi'
    rw [basisOf_apply, basisOf_apply, flip_apply_ne S i i' (fun h => hi' (Fin.ext h))]
  · rw [basisOf_apply, flip_apply_self]
    unfold nb
    rcases Bool.eq_false_or_eq_true (S i) with h | h <;> simp [h]

/-- A pattern with no improving pair is optimal-terminal. -/
lemma isOptimalTerminal (n : ℕ) (S : ℕ → Bool) (hall : ∀ p < n, sg S p ≠ sg S n) :
    IsSimplexOptimalTerminal (kleeMintyA n) (kleeMintyc n) (basisOf n S) := by
  intro j hj
  rw [nb_of_not_mem n S j hj, reducedCost_nb]
  have := sg_mul_sg_eq_neg_one_of_ne S n (pairIdx n j)
    (fun h => hall _ (pairIdx_lt n j) h.symm)
  rw [mul_assoc, this]
  have : (0 : ℝ) < 10 ^ (n - 1 - pairIdx n j) := by positivity
  linarith

end SmaleNinth.KM

/-!
The Klee–Minty trajectory: the binary reflected Gray code of the step index
gives the pattern, and the whole run of `2ⁿ − 1` Dantzig pivots is assembled.
-/

open Matrix LinearOptimization

namespace SmaleNinth.KM

lemma gray_zero : gray 0 = fun _ => false := by
  funext i; simp [gray]

lemma T_const_false (i : ℕ) : T (fun _ => false) i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [T_succ, ih]; simp

lemma z_const_false (i : ℕ) : z (fun _ => false) i = (10 : ℝ) ^ i := by
  simp [z, T_const_false]

lemma basisOf_zero (n : ℕ) : basisOf n (gray 0) = kleeMintySlackBasis n := by
  apply Function.Embedding.ext
  intro i
  rw [basisOf_apply, gray_zero]
  rfl

lemma pointOf_zero (n : ℕ) : pointOf n (gray 0) = kleeMintySlackSolution n := by
  funext j
  simp only [pointOf, kleeMintySlackSolution, gray_zero, Bool.false_eq_true, if_false,
    z_const_false]
  split_ifs
  · rfl
  · rw [← mul_pow]; norm_num

lemma eq_two_pow_sub_one_of_bits (n k : ℕ) (hk : k < 2 ^ n)
    (hall : ∀ i < n, k.testBit i = true) : k = 2 ^ n - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi : i < n
  · simp [hi, hall i hi]
  · have hk2 : k < 2 ^ i :=
      lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hk2]; simp [hi]

/-- Below `2ⁿ − 1` some bit below `n` is zero; take the least such bit. -/
lemma least_zero_bit (n k : ℕ) (hk : k < 2 ^ n - 1) :
    ∃ t, t < n ∧ k.testBit t = false ∧ ∀ p < t, k.testBit p = true := by
  have h2n : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  have hk' : k < 2 ^ n := by omega
  have hex : ∃ t, k.testBit t = false := by
    by_contra h
    have hall : ∀ t, k.testBit t = true := fun t => by
      by_contra h'; exact h ⟨t, by simpa using h'⟩
    have := eq_two_pow_sub_one_of_bits n k hk' (fun i _ => hall i)
    omega
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun p hp => ?_⟩
  · by_contra hge
    have hge' : n ≤ Nat.find hex := not_lt.mp hge
    have := eq_two_pow_sub_one_of_bits n k hk' (fun i hi => by
      have : k.testBit i ≠ false := Nat.find_min hex (by omega)
      simpa using this)
    omega
  · have : k.testBit p ≠ false := Nat.find_min hex hp
    simpa using this

/-- Incrementing the step flips the Gray pattern at the least zero bit. -/
lemma gray_succ (k t : ℕ) (hlow : ∀ i < t, k.testBit i = true) (ht : k.testBit t = false) :
    gray (k + 1) = flip (gray k) t := by
  funext i
  unfold gray flip
  rw [testBit_succ_of_trailing t k hlow ht i, testBit_succ_of_trailing t k hlow ht (i + 1)]
  rcases lt_trichotomy i t with h | h | h
  · by_cases h2 : i + 1 < t
    · simp [h, h2, show i ≠ t by omega, hlow i h, hlow (i + 1) h2]
    · have h3 : i + 1 = t := by omega
      subst h3
      simp [h, hlow i h, ht]
  · subst h
    simp [show ¬ (i + 1 < i) by omega, ht]
  · simp [show ¬ (i < t) by omega, show i ≠ t by omega, show ¬ (i + 1 < t) by omega,
      show i + 1 ≠ t by omega]

/-- For `k < 2ⁿ`, pair `i` is improving iff bit `i` of `k` is zero. -/
lemma sg_gray_eq_iff (k i n : ℕ) (hkn : k < 2 ^ n) :
    sg (gray k) i = sg (gray k) n ↔ k.testBit i = false := by
  rw [sg_gray, sg_gray, Nat.testBit_lt_two_pow hkn]
  rcases Bool.eq_false_or_eq_true (k.testBit 0) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (k.testBit i) with h1 | h1 <;> simp [h0, h1] <;> norm_num

/-- The trajectory. -/
noncomputable def traj (n : ℕ) (k : ℕ) : (Fin n ↪ Fin (2 * n)) × (Fin (2 * n) → ℝ) :=
  (basisOf n (gray k), pointOf n (gray k))

theorem klee_minty (n : ℕ) :
    ∃ f : ℕ → (Fin n ↪ Fin (2 * n)) × (Fin (2 * n) → ℝ),
      (f 0).1 = kleeMintySlackBasis n ∧
      (f 0).2 = kleeMintySlackSolution n ∧
      (∀ k ≤ 2 ^ n - 1,
        IsSimplexState (kleeMintyA n) (kleeMintyb n) (f k).1 (f k).2) ∧
      (∀ k < 2 ^ n - 1,
        IsDantzigPivot (kleeMintyA n) (kleeMintyc n) (f k).1 (f k).2
          (f (k + 1)).1 (f (k + 1)).2) ∧
      IsSimplexOptimalTerminal (kleeMintyA n) (kleeMintyc n)
        (f (2 ^ n - 1)).1 := by
  refine ⟨traj n, basisOf_zero n, pointOf_zero n, fun k _ => isSimplexState n (gray k), ?_, ?_⟩
  · intro k hk
    obtain ⟨t, htn, ht, hlow⟩ := least_zero_bit n k hk
    have h2n : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have hk2 : k < 2 ^ n := by omega
    show IsDantzigPivot (kleeMintyA n) (kleeMintyc n) (basisOf n (gray k)) (pointOf n (gray k))
      (basisOf n (gray (k + 1))) (pointOf n (gray (k + 1)))
    rw [gray_succ k t hlow ht]
    apply isDantzigPivot n (gray k) t htn
    · intro p hp
      rw [Ne, sg_gray_eq_iff k p n hk2, hlow p hp]
      simp
    · rw [sg_gray_eq_iff k t n hk2]; exact ht
  · show IsSimplexOptimalTerminal (kleeMintyA n) (kleeMintyc n) (basisOf n (gray (2 ^ n - 1)))
    apply isOptimalTerminal
    intro p hp
    have h2n : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have hk2 : 2 ^ n - 1 < 2 ^ n := by omega
    rw [Ne, sg_gray_eq_iff _ p n hk2, Nat.testBit_two_pow_sub_one]
    simp [hp]

end SmaleNinth.KM

open SmaleNinth Matrix LinearOptimization

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : ℕ → (Fin n ↪ Fin (2 * n)) × (Fin (2 * n) → ℝ),
      (f 0).1 = kleeMintySlackBasis n ∧
      (f 0).2 = kleeMintySlackSolution n ∧
      (∀ k ≤ 2 ^ n - 1,
        IsSimplexState (kleeMintyA n) (kleeMintyb n) (f k).1 (f k).2) ∧
      (∀ k < 2 ^ n - 1,
        IsDantzigPivot (kleeMintyA n) (kleeMintyc n) (f k).1 (f k).2
          (f (k + 1)).1 (f (k + 1)).2) ∧
      IsSimplexOptimalTerminal (kleeMintyA n) (kleeMintyc n)
        (f (2 ^ n - 1)).1 :=
  SmaleNinth.KM.klee_minty n
