-- Prove2me | solution 1 for PosIndexNash.PPADS.constant_shift_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:54:10.067255+00:00
-- url     : https://prove2.me/submissions/9ffb308f-60b4-41b4-9fbe-c2adcc7635ca

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_ShapleyIndex
import Definitions.Def_PosIndexNash_PPADS_Nondegenerate
import Definitions.Def_QuasiStrictNE_IsNE

namespace PosIndexNash.PPADS

open QuasiStrictNE Matrix

private lemma br1_add_const_aux {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) {y : Fin n → ℝ}
    (hy : y ∈ stdSimplex ℝ (Fin n)) : BR1 (A + Matrix.of fun _ _ => c) y = BR1 A y := by
  have hmul (i : Fin m) : ((A + Matrix.of fun _ _ => c) *ᵥ y) i = (A *ᵥ y) i + c := by
    calc
      ((A + Matrix.of fun _ _ => c) *ᵥ y) i = (A *ᵥ y) i + ∑ j, c * y j := by
        simp [Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
      _ = (A *ᵥ y) i + c * ∑ j, y j :=
        congrArg ((A *ᵥ y) i + ·) (Finset.mul_sum Finset.univ (fun j => y j) c).symm
      _ = (A *ᵥ y) i + c := by rw [hy.2, mul_one]
  ext i
  simp only [BR1, Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [hmul]
  exact forall_congr' fun _ => add_le_add_iff_right c

private lemma br2_add_const_aux {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) {x : Fin m → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin m)) : BR2 (B + Matrix.of fun _ _ => c) x = BR2 B x := by
  have hmul (j : Fin n) : (x ᵥ* (B + Matrix.of fun _ _ => c)) j = (x ᵥ* B) j + c := by
    calc
      (x ᵥ* (B + Matrix.of fun _ _ => c)) j = (x ᵥ* B) j + ∑ i, x i * c := by
        simp [Matrix.vecMul, dotProduct, mul_add, Finset.sum_add_distrib]
      _ = (x ᵥ* B) j + (∑ i, x i) * c :=
        congrArg ((x ᵥ* B) j + ·) (Finset.sum_mul Finset.univ (fun i => x i) c).symm
      _ = (x ᵥ* B) j + c := by rw [hx.2, one_mul]
  ext j
  simp only [BR2, Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [hmul]
  exact forall_congr' fun _ => add_le_add_iff_right c

private lemma nondegenerate_add_const_aux {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) :
    Nondegenerate (A + Matrix.of fun _ _ => c) (B + Matrix.of fun _ _ => c) ↔ Nondegenerate A B := by
  constructor <;> intro h
  · unfold Nondegenerate at h ⊢
    intro x hx y hy
    simpa only [br2_add_const_aux B c hx, br1_add_const_aux A c hy] using h x hx y hy
  · unfold Nondegenerate at h ⊢
    intro x hx y hy
    simpa only [br2_add_const_aux B c hx, br1_add_const_aux A c hy] using h x hx y hy

private lemma borderedDet_add_const_aux {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (c : ℝ) :
    borderedDet (C + Matrix.of fun _ _ => c) = borderedDet C := by
  let negOnes : Matrix (Fin k) (Fin 1) ℝ := Matrix.of fun _ _ => (-1 : ℝ)
  let ones : Matrix (Fin 1) (Fin k) ℝ := Matrix.of fun _ _ => (1 : ℝ)
  let E : Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℝ :=
    Matrix.fromBlocks 1 0 (Matrix.of fun _ _ => -c) 1
  have hmul : Matrix.fromBlocks C negOnes ones 0 * E =
      Matrix.fromBlocks (C + Matrix.of fun _ _ => c) negOnes ones 0 := by
    rw [Matrix.fromBlocks_multiply]
    simp only [negOnes, ones, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    congr 2
    ext i j
    simp [Matrix.mul_apply]
  change (Matrix.fromBlocks (C + Matrix.of fun _ _ => c) negOnes ones 0).det =
    (Matrix.fromBlocks C negOnes ones 0).det
  rw [← hmul, Matrix.det_mul]
  simp [E]

private lemma shapleyIndex_add_const_aux {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    shapleyIndex (A + Matrix.of fun _ _ => c) (B + Matrix.of fun _ _ => c) x y = shapleyIndex A B x y := by
  unfold shapleyIndex
  split_ifs with h
  · dsimp only
    have hA : (A + Matrix.of fun _ _ => c).submatrix
        ((supp x).orderEmbOfFin rfl) ((supp y).orderEmbOfFin h) =
        A.submatrix ((supp x).orderEmbOfFin rfl) ((supp y).orderEmbOfFin h) +
          Matrix.of fun _ _ => c := rfl
    have hB : ((B + Matrix.of fun _ _ => c).submatrix
        ((supp x).orderEmbOfFin rfl) ((supp y).orderEmbOfFin h)).transpose =
        (B.submatrix ((supp x).orderEmbOfFin rfl) ((supp y).orderEmbOfFin h)).transpose +
          Matrix.of fun _ _ => c := rfl
    rw [hA, hB, borderedDet_add_const_aux, borderedDet_add_const_aux]
  · rfl

end PosIndexNash.PPADS

open PosIndexNash.PPADS QuasiStrictNE Matrix

theorem solution {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) :
    (Nondegenerate (A + Matrix.of fun _ _ => c) (B + Matrix.of fun _ _ => c) ↔ Nondegenerate A B) ∧
    (∀ x y, shapleyIndex (A + Matrix.of fun _ _ => c) (B + Matrix.of fun _ _ => c) x y = shapleyIndex A B x y) ∧
    (∀ x y, x ∈ stdSimplex ℝ (Fin m) → y ∈ stdSimplex ℝ (Fin n) →
      (QuasiStrictNE.IsNE (A + Matrix.of fun _ _ => c) (B + Matrix.of fun _ _ => c) x y ↔
        QuasiStrictNE.IsNE A B x y)) := by
  refine ⟨PosIndexNash.PPADS.nondegenerate_add_const_aux A B c,
    PosIndexNash.PPADS.shapleyIndex_add_const_aux A B c, ?_⟩
  intro x y hx hy
  simp only [QuasiStrictNE.IsNE, hx, hy, true_and,
    PosIndexNash.PPADS.br1_add_const_aux A c hy, PosIndexNash.PPADS.br2_add_const_aux B c hx]
