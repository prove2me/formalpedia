-- Prove2me | solution 1 for ShapleySnowSG.Kernel.lemma_B1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:44:59.148069+00:00
-- url     : https://prove2.me/submissions/07e9f408-cefa-4174-934e-d1667b83de44

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

open Matrix

namespace SSKAux
open ShapleySnowSG.Kernel

lemma onesMat_eq {m : Type*} [Fintype m] (w : ℝ) :
    w • onesMat m m = replicateCol Unit (fun _ => w) * replicateRow Unit (fun _ => (1 : ℝ)) := by
  ext i j
  simp [onesMat, replicateCol, replicateRow, Matrix.mul_apply]

lemma B1_inv {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) (hA : A.det ≠ 0) (w : ℝ) :
    (A + w • onesMat m m).det = A.det + w * Ssum (co A) := by
  rw [onesMat_eq, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hA),
    Matrix.det_unique (n := Unit), inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
    replicateCol_apply, Matrix.smul_apply, smul_eq_mul, one_mul, Ssum, co, transpose_apply,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [Finset.sum_mul, mul_add, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  field_simp

lemma B1_i {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (w : ℝ) :
    (M + w • onesMat m m).det = M.det + w * Ssum (co M) := by
  let A : ℝ → Matrix m m ℝ := fun t => M + t • (1 : Matrix m m ℝ)
  have hA : ∀ t, (A t).det = (-M).charpoly.eval t := by
    intro t
    rw [eval_charpoly, sub_neg_eq_add, add_comm]
    simp [A, Matrix.scalar_apply, smul_one_eq_diagonal]
  have hfin : {t : ℝ | ((-M).charpoly).IsRoot t}.Finite :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic _).ne_zero
  have hdense : Dense {t : ℝ | ((-M).charpoly).IsRoot t}ᶜ := hfin.countable.dense_compl ℝ
  have hcA : Continuous A := continuous_const.add (continuous_id.smul continuous_const)
  let g : ℝ → ℝ := fun t => (A t + w • onesMat m m).det - (A t).det - w * Ssum (co (A t))
  have hg : Continuous g := by
    refine ((hcA.add continuous_const).matrix_det.sub hcA.matrix_det).sub
      (continuous_const.mul ?_)
    simp only [Ssum, co, transpose_apply]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact hcA.matrix_adjugate.matrix_elem _ _
  have heq : g = fun _ => 0 := by
    refine Continuous.ext_on hdense hg continuous_const fun t ht => ?_
    have hne : (A t).det ≠ 0 := by
      rw [hA]; exact ht
    simp only [g, B1_inv (A t) hne w]
    ring
  have h0 := congrFun heq 0
  simp only [g, A, zero_smul, add_zero] at h0
  linarith

lemma B1_iii_row {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (l : m) :
    (co M *ᵥ fun _ => (1 : ℝ)) l = (M.updateRow l (fun _ => 1)).det := by
  rw [det_eq_sum_mul_adjugate_row _ l]
  simp only [mulVec, dotProduct, co, transpose_apply, mul_one, updateRow_self, one_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [adjugate_apply, adjugate_apply, updateRow_idem]

lemma B1_iii {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (w : ℝ) :
    co (M + w • onesMat m m) *ᵥ (fun _ => (1 : ℝ)) = co M *ᵥ (fun _ => (1 : ℝ)) := by
  ext l
  rw [B1_iii_row, B1_iii_row]
  let u : m → ℝ := fun i => if i = l then 0 else 1
  let v : m → ℝ := w • Pi.single l 1
  have hL : (1 + replicateCol Unit u * replicateRow Unit v).det = 1 := by
    rw [det_one_add_replicateCol_mul_replicateRow, add_eq_left]
    refine Finset.sum_eq_zero fun x _ => ?_
    simp only [v, u, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hprod : (M + w • onesMat m m).updateRow l (fun _ => 1) =
      (1 + replicateCol Unit u * replicateRow Unit v) * M.updateRow l (fun _ => 1) := by
    have hcv : ∀ i j, (replicateCol Unit u * replicateRow Unit v * M.updateRow l (fun _ => 1)) i j
        = u i * w := by
      intro i j
      rw [Matrix.mul_assoc]
      simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique,
        Finset.sum_singleton, v, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, updateRow_self]
    ext i j
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, hcv]
    by_cases hi : i = l
    · subst hi
      simp [u, updateRow_self]
    · simp [updateRow_ne hi, u, hi, onesMat]
  rw [hprod, det_mul, hL, one_mul]

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) :
    (∀ w : ℝ, (M + w • onesMat m m).det = M.det + w * Ssum (co M)) ∧
    (∀ w : ℝ, Ssum (co (M + w • onesMat m m)) = Ssum (co M)) ∧
    (∀ w : ℝ, co (M + w • onesMat m m) *ᵥ (fun _ => (1 : ℝ)) = co M *ᵥ (fun _ => (1 : ℝ))) ∧
    (∀ w : ℝ, (co (M + w • onesMat m m))ᵀ *ᵥ (fun _ => (1 : ℝ)) =
      (co M)ᵀ *ᵥ (fun _ => (1 : ℝ))) := by
  refine ⟨SSKAux.B1_i M, fun w => ?_, SSKAux.B1_iii M, fun w => ?_⟩
  · rcases eq_or_ne w 0 with hw | hw
    · subst hw; simp
    · have h1 := SSKAux.B1_i M w
      have h2 := SSKAux.B1_i (M + w • onesMat m m) (-w)
      have h3 : M + w • onesMat m m + (-w) • onesMat m m = M := by
        rw [neg_smul, add_neg_cancel_right]
      rw [h3, h1] at h2
      have : w * (Ssum (co M) - Ssum (co (M + w • onesMat m m))) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hw
      · linarith
  · have hT : ∀ N : Matrix m m ℝ, (co N)ᵀ = co Nᵀ := fun N => by
      simp [co, adjugate_transpose]
    have hU : (M + w • onesMat m m)ᵀ = Mᵀ + w • onesMat m m := by
      ext i j; simp [onesMat]
    rw [hT, hT, hU]
    exact SSKAux.B1_iii Mᵀ w
