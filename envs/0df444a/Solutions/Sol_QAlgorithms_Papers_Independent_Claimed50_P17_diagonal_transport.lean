-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.diagonal_transport
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:14:10.724508+00:00
-- url     : https://prove2.me/submissions/45ffa459-c650-4e1b-86c3-f76ec502998c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

theorem g57d_dephase_psd {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    Matrix.PosSemidef (Matrix.of fun a b => if f a = f b then M a b else 0 : Matrix ι ι ℂ) := by
  have key : (Matrix.of fun a b => if f a = f b then M a b else 0 : Matrix ι ι ℂ) =
      ∑ k : κ, (Matrix.diagonal (fun a => if f a = k then (1:ℂ) else 0))ᴴ * M *
        Matrix.diagonal (fun a => if f a = k then (1:ℂ) else 0) := by
    ext a b
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    by_cases h : f a = f b
    · rw [if_pos h, Finset.sum_eq_single (f a)]
      · simp [h]
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    · rw [if_neg h]
      refine (Finset.sum_eq_zero (fun k _ => ?_)).symm
      by_cases h1 : f a = k
      · have : f b ≠ k := fun h2 => h (h1.trans h2.symm)
        simp [this]
      · simp [h1]
  rw [key]
  exact Matrix.posSemidef_sum _ (fun k _ => hM.conjTranspose_mul_mul_same _)

theorem solution (d : ℕ) (hd : 2 ≤ d) (timing : Timing) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy timing R) :
    IsReplicationStrategy timing (dephaseClassicalOutput R) ∧
    (∀ i j k, (diagonalBlocks R i j k).PosSemidef) ∧
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ i j, replica (dephaseClassicalOutput R) U i j = replica R U i j) ∧
    haarReplicationScore (dephaseClassicalOutput R) = haarReplicationScore R := by
  have hrep : ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ i j,
      replica (dephaseClassicalOutput R) U i j = replica R U i j := by
    intro U i j
    ext x y
    simp [replica, dephaseClassicalOutput,
      QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput]
  have hsum : (∑ i, ∑ j, dephaseClassicalOutput R i j) =
      QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput (∑ i, ∑ j, R i j) := by
    ext x y
    simp only [Matrix.sum_apply, dephaseClassicalOutput,
      QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput]
    split_ifs <;> simp
  refine ⟨⟨fun i j => g57d_dephase_psd (fun p : ABCD d => p.2) _ (hR.1 i j), ?_⟩, ?_, hrep, ?_⟩
  · cases timing with
    | cloning =>
      obtain ⟨S, hS, hS1, hS2⟩ := hR.2
      refine ⟨S, hS, hS1, ?_⟩
      rw [hsum, hS2]
      ext x y
      simp only [QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput, cloningTotal,
        Matrix.kronecker_apply, Matrix.one_apply]
      split_ifs <;> simp_all
    | learning =>
      obtain ⟨S, hS, hS1, hS2⟩ := hR.2
      refine ⟨S, hS, hS1, ?_⟩
      rw [hsum, hS2]
      ext x y
      simp only [QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput, learningTotal]
      split_ifs <;> simp_all
  · intro i j k
    have := (hR.1 i j).submatrix (fun x : ABC d => (x, k))
    exact this
  · unfold haarReplicationScore scoreIntegrand
    simp only [hrep]
