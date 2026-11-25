-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.altBranch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:28.052804+00:00
-- url     : https://prove2.me/submissions/72c9ddb2-0efd-45fe-a551-75a8c830f42d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_prod_zpow_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_tele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution : AltBranchStatement := by
  intro K _ n lam hlam t ht
  set y := t (Fin.last n) with hy_def
  have hy : y ≠ 0 := ht _
  set a : Fin (n + 1) → ℤ := lam + delta (n + 1) with ha
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of fun i j => t i ^ a j with hM
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of fun k j =>
    if k = j then 1 else if (k : ℕ) = (j : ℕ) + 1 then -(y ^ (a j - a k)) else 0 with hU_def
  have hU : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular U ?_]
    · simp [U]
    · intro k j hkj
      have hkj' : k < j := OrderDual.toDual_lt_toDual.mp hkj
      have hv := Fin.lt_def.mp hkj'
      simp only [U, Matrix.of_apply]
      rw [if_neg (ne_of_lt hkj'), if_neg (by omega)]
  have hexp1 : ∀ j : Fin n, a j.castSucc = lam j.castSucc + 1 + delta n j := by
    intro j; simp only [ha, Pi.add_apply, delta, Fin.val_castSucc]; push_cast; ring
  have hexp2 : ∀ j : Fin n, a j.succ = lam j.succ + delta n j := by
    intro j; simp only [ha, Pi.add_apply, delta, Fin.val_succ]; push_cast; ring
  have hexpl : a (Fin.last n) = lam (Fin.last n) := by
    simp only [ha, Pi.add_apply, delta, Fin.val_last]; push_cast; ring
  have hMU_last : ∀ i, (M * U) i (Fin.last n) = t i ^ a (Fin.last n) := by
    intro i
    rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.last n)]
    · simp [M, U]
    · intro k hk
      have hk' := Fin.is_le k
      simp only [U, Matrix.of_apply, if_neg hk]
      rw [if_neg (by simp only [Fin.val_last]; omega), mul_zero]
  have hMU_cs : ∀ i (j : Fin n), (M * U) i j.castSucc =
      t i ^ a j.castSucc - y ^ (a j.castSucc - a j.succ) * t i ^ a j.succ := by
    intro i j
    have hne : j.castSucc ≠ j.succ := by simp [Fin.ext_iff]
    rw [Matrix.mul_apply, Fintype.sum_eq_add j.castSucc j.succ hne]
    · have h2 : ((j.succ : Fin (n + 1)) : ℕ) = (j.castSucc : ℕ) + 1 := by simp
      have hU1 : U j.castSucc j.castSucc = 1 := by simp [U]
      have hU2 : U j.succ j.castSucc = -(y ^ (a j.castSucc - a j.succ)) := by
        simp only [U, Matrix.of_apply]; rw [if_neg hne.symm, if_pos h2]
      rw [hU1, hU2]; simp only [M, Matrix.of_apply]; ring
    · rintro k ⟨hk1, hk2⟩
      simp only [U, Matrix.of_apply, if_neg hk1]
      rw [if_neg, mul_zero]
      intro h; apply hk2; ext; simp only [Fin.val_castSucc, Fin.val_succ] at h ⊢; omega

  have hrow : ∀ j : Fin n, (M * U) (Fin.last n) j.castSucc = 0 := by
    intro j
    rw [hMU_cs, ← zpow_add₀ hy, sub_add_cancel, sub_self]

  set S : Matrix (Fin n) (Fin n) K := Matrix.of fun i j =>
    ∑ m ∈ Icc (lam j.succ) (lam j.castSucc), t i.castSucc ^ (m + delta n j) * y ^ (lam j.castSucc - m) with hS
  have hminor : (M * U).submatrix Fin.castSucc Fin.castSucc =
      Matrix.of fun i j => (t i.castSucc - y) * S i j := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hMU_cs, S]
    rw [tele (ht _) hy (lam j.succ) (lam j.castSucc) (delta n j)
      (by have := hlam (Fin.castSucc_le_succ j); omega)]
    rw [hexp1, hexp2]
    congr 2
    ring
  have hSdet : S.det = ∑ mu ∈ interl lam,
      (∏ j : Fin n, y ^ (lam j.castSucc - mu j)) * alt n (mu + delta n) (fun i => t i.castSucc) := by
    rw [← Matrix.det_transpose]
    have hT : S.transpose = fun j => ∑ m ∈ Icc (lam j.succ) (lam j.castSucc),
        (fun i => t i.castSucc ^ (m + delta n j) * y ^ (lam j.castSucc - m)) := by
      ext j i; simp [S, Matrix.transpose_apply, Finset.sum_apply]
    rw [hT]
    have := (Matrix.detRowAlternating (R := K) (n := Fin n)).toMultilinearMap.map_sum_finset
      (fun j m => fun i => t i.castSucc ^ (m + delta n j) * y ^ (lam j.castSucc - m))
      (fun j => Icc (lam j.succ) (lam j.castSucc))
    refine (this.trans ?_)
    refine sum_congr rfl fun mu _ => ?_
    show Matrix.det (Matrix.of fun j i => t i.castSucc ^ (mu j + delta n j) * y ^ (lam j.castSucc - mu j)) = _
    rw [← Matrix.det_transpose]
    have hT2 : Matrix.transpose (Matrix.of fun j i => t i.castSucc ^ (mu j + delta n j) * y ^ (lam j.castSucc - mu j) :
        Matrix (Fin n) (Fin n) K) =
        Matrix.of fun i j => y ^ (lam j.castSucc - mu j) * t i.castSucc ^ ((mu + delta n) j) := by
      ext i j; simp [Matrix.transpose_apply, mul_comm]
    rw [hT2]
    have hmr := Matrix.det_mul_row (fun j => y ^ (lam j.castSucc - mu j))
      (Matrix.of fun i j => t i.castSucc ^ (mu + delta n) j)
    simp only [Matrix.of_apply] at hmr
    rw [hmr]
    rfl

  have hdet : alt (n + 1) a t = (M * U).det := by
    rw [Matrix.det_mul, hU, mul_one]; rfl
  rw [hdet, Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp only [hrow, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last, hMU_last]
  rw [hminor, Matrix.det_mul_column, hSdet, Fin.val_last]
  have hsign : ((-1 : K) ^ (n + n)) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [hsign, one_mul, hexpl, mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun mu _ => ?_
  rw [prod_zpow_eq hy]
  have hw : wsum lam - wsum mu = lam (Fin.last n) + ∑ j : Fin n, (lam j.castSucc - mu j) := by
    simp only [wsum, Fin.sum_univ_castSucc, Finset.sum_sub_distrib]; ring
  rw [hw, zpow_add₀ hy]
  ring
end ReciprocityTheory.ChartRestriction.TR.Weyl
