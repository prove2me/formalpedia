-- Prove2me | solution 1 for RobustSpecClust.Round.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-17T10:58:02.720736+00:00
-- url     : https://prove2.me/submissions/3794e012-edf5-48bf-97ee-e3dbe379f392

import Theorems.Thm_RobustSpecClust_Round_eq_G6
import Theorems.Thm_RobustSpecClust_Round_lemma_5
import Theorems.Thm_RobustSpecClust_Round_bstar_sep

open RobustSpecClust.Round Matrix

theorem solution {n r : ℕ} [NeZero r] (φ : Fin n → Fin r) (hφ : ∀ k, 0 < clusterSize φ k)
    (Xh : Matrix (Fin n) (Fin n) ℝ) (hsym : Xhᵀ = Xh) (hbox : ∀ i j, 0 ≤ Xh i j ∧ Xh i j ≤ 1)
    (Uh : Matrix (Fin n) (Fin r) ℝ) (hU : IsTopEigvecs Xh Uh)
    (ε : ℝ) (hε : 0 < ε) (a : Fin n → Fin r) (B : Matrix (Fin r) (Fin r) ℝ)
    (hkm : IsApproxKMeans ε Uh a B)
    (O : Matrix (Fin r) (Fin r) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin r) ℝ)
    (hOopt : ∀ O' ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      frobSq (Uh - U0 φ * O) ≤ frobSq (Uh - U0 φ * O')) :
    ∑ k, ((misSet (U0 φ * O) (memb a * B) φ (fun k => 1 / Real.sqrt (clusterSize φ k)) k).card
        : ℝ) / clusterSize φ k
      ≤ 64 * (2 + ε) * l1 (trueClust φ - Xh) / nmin φ ^ 2 := by
  -- `U⁰ = Θ(φ) Diag(1/√n_k)`, so `V = U⁰O = Θ(φ) B*` with `B* = Diag(1/√n_k) O`
  have hU0 : U0 φ = memb φ * Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) := by
    ext i k
    rw [mul_diagonal]
    simp only [U0, memb]
    split_ifs <;> simp
  have hV : memb φ * (Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) * O)
      = U0 φ * O := by
    rw [hU0, Matrix.mul_assoc]
  -- `δ_k = 1/√n_k` is admissible in Lemma 5, by the separation of the rows of `B*`
  have hδ0 : ∀ k, 0 ≤ (fun k => 1 / Real.sqrt (clusterSize φ k : ℝ)) k := fun k => by
    show 0 ≤ 1 / Real.sqrt (clusterSize φ k : ℝ)
    positivity
  have hδ : ∀ k l, l ≠ k → (fun k => 1 / Real.sqrt (clusterSize φ k : ℝ)) k ≤
      vecNorm ((Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) * O) l -
        (Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) * O) k) := by
    intro k l hlk
    rw [bstar_sep φ hφ O hO k l (Ne.symm hlk)]
    show 1 / Real.sqrt (clusterSize φ k : ℝ) ≤ _
    rw [one_div, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    have : (0 : ℝ) ≤ 1 / (clusterSize φ l : ℝ) := by positivity
    rw [one_div] at this ⊢
    rw [one_div]
    linarith
  -- Lemma 5 applied to `V = U⁰O`, `V̂ = Û`
  have h5 := lemma_5 φ (Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) * O) Uh ε hε
    a B hkm (fun k => 1 / Real.sqrt (clusterSize φ k : ℝ)) hδ0 hδ
  rw [hV] at h5
  -- (G.6)
  have h6 := eq_G6 φ hφ Xh hsym hbox Uh hU O hO hOopt
  have hlhs : ∑ k, ((misSet (U0 φ * O) (memb a * B) φ
        (fun k => 1 / Real.sqrt (clusterSize φ k)) k).card : ℝ) / clusterSize φ k
      = ∑ k, ((misSet (U0 φ * O) (memb a * B) φ
        (fun k => 1 / Real.sqrt (clusterSize φ k)) k).card : ℝ)
          * (1 / Real.sqrt (clusterSize φ k : ℝ)) ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _), mul_one_div]
  have hfs : frobSq (U0 φ * O - Uh) = frobSq (Uh - U0 φ * O) := by
    unfold frobSq
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply]; ring
  have hl1 : l1 (Xh - trueClust φ) = l1 (trueClust φ - Xh) := by
    unfold l1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply]; exact abs_sub_comm _ _
  rw [hfs] at h5
  rw [hl1] at h6
  rw [hlhs]
  calc _ ≤ 4 * (4 + 2 * ε) * frobSq (Uh - U0 φ * O) := h5
    _ ≤ 4 * (4 + 2 * ε) * (8 * l1 (trueClust φ - Xh) / nmin φ ^ 2) :=
        mul_le_mul_of_nonneg_left h6 (by linarith)
    _ = 64 * (2 + ε) * l1 (trueClust φ - Xh) / nmin φ ^ 2 := by ring
