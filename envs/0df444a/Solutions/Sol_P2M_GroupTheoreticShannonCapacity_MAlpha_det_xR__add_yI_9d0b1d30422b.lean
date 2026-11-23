-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:46.498798+00:00
-- url     : https://prove2.me/submissions/8192f7ba-d8c7-4ed7-bbef-e72a6b576c19

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
section
namespace GroupTheoreticShannonCapacity.MAlpha
open Matrix
section DetLemmas
private lemma m_add_two_sub_one (m : ℕ) : m + 2 - 1 = m + 1 := by omega
open Finset in
/-- The minor at (0, 0) of xR_α + yI is lower triangular with y on the diagonal -/
private lemma minor00_lowerTriangular (m : ℕ) (x y α : ℝ) :
    ((x • Rα (m + 2) α + y • 1).submatrix Fin.succ (0 : Fin (m + 2)).succAbove).BlockTriangular
      (EquivLike.toFunLike.coe OrderDual.toDual) := by
  intro i j (hij : (OrderDual.toDual j) < (OrderDual.toDual i))
  -- hij means j > i in the original order
  simp only [OrderDual.toDual_lt_toDual] at hij
  simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Rα,
             Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
             Matrix.of_apply, smul_eq_mul, Fin.val_succ]
  -- Need to show entry is 0 when i < j (in natural order)
  -- Entry (i, j) = x * R_α[i+1, j+1] + y * δ_{i,j}
  -- For i < j: not diagonal (i ≠ j), not subdiagonal (i+1 ≠ j+2)
  rw [m_add_two_sub_one]
  have h1 : ¬(i.val + 1 = 0 ∧ j.val + 1 = m + 1) := by omega
  have h2 : ¬(i.val + 1 = j.val + 1 + 1) := by omega
  have h3 : i.succ ≠ j.succ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_succ]
    omega
  simp only [h1, h2, ↓reduceIte, mul_zero, h3, zero_add]
open Finset in
/-- The minor at (0, 0) has y on the diagonal -/
private lemma minor00_diag (m : ℕ) (x y α : ℝ) (i : Fin (m + 1)) :
    (x • Rα (m + 2) α + y • 1).submatrix Fin.succ (0 : Fin (m + 2)).succAbove i i = y := by
  simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Rα,
             Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
             Matrix.of_apply, smul_eq_mul, Fin.val_succ, m_add_two_sub_one]
  have h1 : ¬(i.val + 1 = 0 ∧ i.val + 1 = m + 1) := by omega
  have h2 : ¬(i.val + 1 = i.val + 1 + 1) := by omega
  simp only [h1, h2, ↓reduceIte, mul_zero, mul_one, zero_add]
open Finset in
/-- The minor at (0, n-1) of xR_α + yI is upper triangular with x on the diagonal -/
private lemma minor0n_upperTriangular (m : ℕ) (x y α : ℝ) :
    ((x • Rα (m + 2) α + y • 1).submatrix Fin.succ
      (Fin.last (m + 1)).succAbove).BlockTriangular id := by
  intro i j (hij : j < i)
  simp only [Matrix.submatrix_apply, Rα,
             Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
             Matrix.of_apply, smul_eq_mul]
  -- Need to show entry is 0 when j < i
  -- Entry (i, j) in minor = M[i+1, succAbove(last) j] = M[i+1, j]
  -- since j < m+1 = Fin.last, succAbove maps j to j
  have hj_lt : j.val < m + 1 := j.isLt
  have succAbove_eq : (Fin.last (m + 1)).succAbove j = j.castSucc := by
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_last, hj_lt, ↓reduceIte]
  rw [succAbove_eq]
  simp only [Fin.val_succ, Fin.val_castSucc, m_add_two_sub_one]
  have h1 : ¬(i.val + 1 = 0 ∧ j.val = m + 1) := by omega
  have h2 : ¬(i.val + 1 = j.val + 1) := by omega
  have h4 : i.succ ≠ j.castSucc := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  simp only [h1, h2, ↓reduceIte, mul_zero, h4, add_zero]
open Finset in
/-- The minor at (0, n-1) has x on the diagonal -/
private lemma minor0n_diag (m : ℕ) (x y α : ℝ) (i : Fin (m + 1)) :
    (x • Rα (m + 2) α + y • 1).submatrix Fin.succ (Fin.last (m + 1)).succAbove i i = x := by
  simp only [Matrix.submatrix_apply, Rα,
             Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
             Matrix.of_apply, smul_eq_mul]
  have hi_lt : i.val < m + 1 := i.isLt
  have succAbove_eq : (Fin.last (m + 1)).succAbove i = i.castSucc := by
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_last, hi_lt, ↓reduceIte]
  rw [succAbove_eq]
  simp only [Fin.val_succ, Fin.val_castSucc, m_add_two_sub_one]
  have h1 : ¬(i.val + 1 = 0 ∧ i.val = m + 1) := by omega
  have h4 : i.succ ≠ i.castSucc := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  simp only [h1, h4, ↓reduceIte, mul_one, mul_zero, add_zero]
end DetLemmas
section DetLemmas2
end DetLemmas2
section ConjugationLemmas
end ConjugationLemmas
section Tests
example : ∀ x y α : ℝ, (x • Rα 2 α + y • 1).det = (-x)^2 * α + y^2 := by
  intro x y α
  simp only [Rα, Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply,
             Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  -- The matrix entries simplify: (0,0)=y, (0,1)=-xα, (1,0)=x, (1,1)=y
  -- det = y*y - (-xα)*x = y² + x²α
  norm_num [Fin.isValue]
  ring
example : Rα 2 (1 : ℝ) = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rα, Matrix.of_apply]
end Tests
end GroupTheoreticShannonCapacity.MAlpha
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (x y α : ℝ) :
    (x • Rα n α + y • 1).det = (-x)^n * α + y^n := by
  -- The proof shows only identity and cyclic shift permutations contribute.
  -- Identity: gives y^n (product of diagonal entries)
  -- Cyclic shift π (i ↦ i-1 mod n): gives sign(π) * (-xα) * x^{n-1} = (-x)^n * α
  -- All other permutations have a zero factor in their product.
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      -- n = 1: direct computation
      -- Matrix is 1×1 with entry (x • Rα 1 α + y • 1)(0,0) = x * (-α) + y * 1
      have h1 : Fintype.card (Fin 1) = 1 := by rfl
      rw [Matrix.det_eq_elem_of_card_eq_one h1 0]
      simp only [Rα, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
                 Matrix.of_apply, smul_eq_mul]
      simp only [Fin.isValue, Fin.val_zero, and_self, ↓reduceIte, mul_neg, mul_one]
      ring
    | succ m =>
      -- n = m + 2 ≥ 2: use Laplace expansion along first row
      have hn_sub : m + 2 - 1 = m + 1 := by omega
      -- Step 1: Apply Laplace expansion
      rw [Matrix.det_succ_row_zero]
      -- The matrix has special structure in row 0
      set M := x • Rα (m + 2) α + y • 1 with hM
      -- Step 2: Compute determinants of the two contributing minors
      -- Minor at (0, 0) is lower triangular with y on diagonal
      have det_minor00 : (M.submatrix Fin.succ (0 : Fin (m + 2)).succAbove).det = y ^ (m + 1) := by
        have htri := minor00_lowerTriangular m x y α
        rw [← hM] at htri
        rw [Matrix.det_of_lowerTriangular _ htri]
        rw [Finset.prod_eq_pow_card (s := Finset.univ) (b := y)]
        · simp only [Finset.card_fin]
        · intro i _
          have := minor00_diag m x y α i
          rw [← hM] at this
          exact this
      -- Minor at (0, last) is upper triangular with x on diagonal
      have det_minor0n : (M.submatrix Fin.succ (Fin.last (m + 1)).succAbove).det = x ^ (m + 1) := by
        have htri := minor0n_upperTriangular m x y α
        rw [← hM] at htri
        rw [Matrix.det_of_upperTriangular htri]
        rw [Finset.prod_eq_pow_card (s := Finset.univ) (b := x)]
        · simp only [Finset.card_fin]
        · intro i _
          have := minor0n_diag m x y α i
          rw [← hM] at this
          exact this
      -- Step 3: Compute entries of row 0
      have entry00 : M 0 0 = y := by
        simp only [hM, Rα, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
                   Matrix.of_apply, smul_eq_mul, Fin.val_zero]
        have h1 : (0 : ℕ) ≠ m + 2 - 1 := by omega
        have h2 : (0 : ℕ) ≠ 0 + 1 := by omega
        simp only [h1, h2, and_false, ↓reduceIte, mul_zero, zero_add, mul_one]
      have entry0n : M 0 (Fin.last (m + 1)) = x * (-α) := by
        simp only [hM, Rα, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
                   Matrix.of_apply, smul_eq_mul, Fin.val_zero, Fin.val_last]
        have h2 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
          omega
        simp only [hn_sub, h2, and_self, ite_false, mul_zero, add_zero, ite_true]
      have entry0_other : ∀ j : Fin (m + 2), j ≠ 0 → j ≠ Fin.last (m + 1) → M 0 j = 0 := by
        intro j hj0 hjn
        simp only [hM, Rα, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
                   Matrix.of_apply, smul_eq_mul, Fin.val_zero]
        rw [hn_sub]
        have hjn' : j.val ≠ m + 1 := by
          intro h
          apply hjn
          exact Fin.ext h
        have hj0' : j.val ≠ 0 := by
          intro h
          apply hj0
          exact Fin.ext h
        have h2 : (0 : ℕ) ≠ j.val + 1 := by omega
        have h3 : (0 : Fin (m + 2)) ≠ j := by exact hj0.symm
        simp only [hjn', and_false, h2, ↓reduceIte, mul_zero, h3, zero_add]
      -- Step 4: The sum over all j, but only j=0 and j=last contribute
      -- We'll compute by breaking the sum
      -- First show that non-contributing terms are 0
      have sum_eq : ∑ j : Fin (m + 2), (-1 : ℝ) ^ j.val * M 0 j *
          (M.submatrix Fin.succ j.succAbove).det =
          M 0 0 * (M.submatrix Fin.succ (0 : Fin (m + 2)).succAbove).det +
          (-1 : ℝ) ^ (m + 1) * M 0 (Fin.last (m + 1)) *
            (M.submatrix Fin.succ (Fin.last (m + 1)).succAbove).det := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ← Finset.sdiff_singleton_eq_erase]
        have hlast_ne_zero : Fin.last (m + 1) ≠ (0 : Fin (m + 2)) := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_zero] at this
          omega
        rw [← Finset.add_sum_erase _ _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
             Finset.notMem_singleton.mpr hlast_ne_zero⟩), ← Finset.sdiff_singleton_eq_erase]
        simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_last]
        -- Remaining sum is 0
        have hz : ∑ x ∈ (Finset.univ \ {0}) \ {Fin.last (m + 1)}, (-1 : ℝ) ^ x.val * M 0 x *
            (M.submatrix Fin.succ x.succAbove).det = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] at hj
          have hj0 : j ≠ 0 := hj.1
          have hjn : j ≠ Fin.last (m + 1) := hj.2
          rw [entry0_other j hj0 hjn]
          ring
        rw [hz, add_zero]
      rw [sum_eq, entry00, entry0n, det_minor00, det_minor0n]
      -- Need to show: y * y^{m+1} + (-1)^{m+1} * (x * -α) * x^{m+1} = (-x)^{m+2} * α + y^{m+2}
      -- LHS = y^{m+2} + (-1)^{m+1} * (-α) * x^{m+2}
      --     = y^{m+2} + (-1)^{m+2} * α * x^{m+2}
      --     = y^{m+2} + (-x)^{m+2} * α = RHS
      have key : (-1 : ℝ) ^ (m + 1) * (x * -α) * x ^ (m + 1) = (-x) ^ (m + 2) * α := by
        calc (-1 : ℝ) ^ (m + 1) * (x * -α) * x ^ (m + 1)
            = (-1) ^ (m + 1) * x ^ (m + 2) * (-α) := by ring
          _ = (-1) ^ (m + 1) * (-1) * x ^ (m + 2) * α := by ring
          _ = (-1) ^ (m + 2) * x ^ (m + 2) * α := by rw [← pow_succ]
          _ = ((-1) * x) ^ (m + 2) * α := by rw [mul_pow]
          _ = (-x) ^ (m + 2) * α := by ring
      rw [key]
      ring
end GroupTheoreticShannonCapacity.MAlpha
