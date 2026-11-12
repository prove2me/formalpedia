-- Prove2me | solution 1 for ProcessingNetworks.EntropyIneq.lemma_B_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:47:05.552391+00:00
-- url     : https://prove2.me/submissions/db8a7e8e-bd63-47a4-a643-c2556494aaa4

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_SectionB4Assumptions
import Theorems.Thm_ProcessingNetworks_EntropyIneq_theorem_F_1

open Filter Topology Matrix ProcessingNetworks.EntropyIneq

private lemma transpose_pow_eq {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) :
    ∀ k : ℕ, (Pᵀ) ^ k = (P ^ k)ᵀ
  | 0 => by simp
  | k + 1 => by rw [pow_succ, pow_succ', transpose_mul, transpose_pow_eq P k]

private lemma vec_nonneg {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hP : ∀ i j, 0 ≤ P i j) :
    ∀ (k : ℕ) (j : Fin I), 0 ≤ ((Pᵀ) ^ k *ᵥ lam) j
  | 0, j => by simpa using hlam j
  | k + 1, j => by
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      exact Finset.sum_nonneg fun r _ => mul_nonneg (hP r j) (vec_nonneg lam P hlam hP k r)

private lemma chain_of_pos {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hP : ∀ i j, 0 ≤ P i j) :
    ∀ (k : ℕ) (j : Fin I), 0 < ((Pᵀ) ^ k *ᵥ lam) j →
      ∃ c : Fin (k + 1) → Fin I,
        0 < lam (c 0) ∧ (∀ m : Fin k, 0 < P (c m.castSucc) (c m.succ)) ∧ c (Fin.last k) = j
  | 0, j, hj => by
      simp only [pow_zero, Matrix.one_mulVec] at hj
      exact ⟨fun _ => j, hj, fun m => m.elim0, rfl⟩
  | k + 1, j, hj => by
      rw [pow_succ', ← Matrix.mulVec_mulVec] at hj
      change 0 < ∑ r : Fin I, Pᵀ j r * ((Pᵀ ^ k *ᵥ lam) r) at hj
      simp only [Matrix.transpose_apply] at hj
      have hex : ∃ r : Fin I, 0 < P r j * ((Pᵀ) ^ k *ᵥ lam) r := by
        by_contra hno
        push Not at hno
        linarith [Finset.sum_nonpos (s := Finset.univ) (fun r _ => hno r)]
      obtain ⟨r, hr_mul⟩ := hex
      have hvr_nonneg : 0 ≤ ((Pᵀ) ^ k *ᵥ lam) r := vec_nonneg lam P hlam hP k r
      have hPrj_pos : 0 < P r j := by
        by_contra hle
        push Not at hle
        have hPrj0 : P r j = 0 := le_antisymm hle (hP r j)
        simp [hPrj0] at hr_mul
      have hvr_pos : 0 < ((Pᵀ) ^ k *ᵥ lam) r := pos_of_mul_pos_right hr_mul (hP r j)
      obtain ⟨c, hc0, hcstep, hclast⟩ := chain_of_pos lam P hlam hP k r hvr_pos
      refine ⟨Fin.snoc c j, ?_, ?_, by simp⟩
      · have h0 : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
        rw [h0, Fin.snoc_castSucc]
        exact hc0
      · intro m
        refine Fin.lastCases ?_ ?_ m
        · rw [Fin.snoc_castSucc, hclast, Fin.succ_last, Fin.snoc_last]
          exact hPrj_pos
        · intro m₀
          rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
          exact hcstep m₀

theorem solution {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (hB4 : SectionB4Assumptions lam P) (i : Fin I) :
    ∃ p : ℕ, ∃ c : Fin (p + 1) → Fin I,
      0 < lam (c 0) ∧ (∀ k : Fin p, 0 < P (c k.castSucc) (c k.succ)) ∧ c (Fin.last p) = i := by
  have hconvP : IsConvergent P := ((theorem_F_1 P).out 1 0).mp hB4.specRadius_lt_one
  have hcontT : Continuous (Matrix.transpose : Matrix (Fin I) (Fin I) ℝ → Matrix (Fin I) (Fin I) ℝ) :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply a).comp (continuous_apply b)
  have hconvPT : IsConvergent Pᵀ := by
    unfold IsConvergent
    have hT := hcontT.continuousAt.tendsto.comp hconvP
    rw [Matrix.transpose_zero] at hT
    have hfn : (fun k : ℕ => (Pᵀ) ^ k) = Matrix.transpose ∘ (fun k : ℕ => P ^ k) := by
      ext k a b
      exact congr_fun (congr_fun (transpose_pow_eq P k) a) b
    rwa [← hfn] at hT
  have hTFAE2 : IsUnit (1 - Pᵀ) ∧
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (Pᵀ) ^ k) atTop (𝓝 (1 - Pᵀ)⁻¹) :=
    ((theorem_F_1 Pᵀ).out 0 2).mp hconvPT
  have hNeumann : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (Pᵀ) ^ k) atTop (𝓝 (1 - Pᵀ)⁻¹) :=
    hTFAE2.2
  have hcontEval : Continuous (fun M : Matrix (Fin I) (Fin I) ℝ => (M *ᵥ lam) i) := by
    have : (fun M : Matrix (Fin I) (Fin I) ℝ => (M *ᵥ lam) i) =
        fun M => ∑ r : Fin I, M i r * lam r := by
      ext M
      simp [Matrix.mulVec, dotProduct]
    rw [this]
    refine continuous_finsetSum _ fun r _ => ?_
    have hentry : Continuous (fun M : Matrix (Fin I) (Fin I) ℝ => M i r) :=
      (continuous_apply r).comp (continuous_apply i : Continuous fun M : Matrix (Fin I) (Fin I) ℝ => M i)
    exact hentry.mul continuous_const
  have hlim_i : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, ((Pᵀ) ^ k *ᵥ lam) i) atTop
      (𝓝 (traffic lam P i)) := by
    unfold traffic
    have h1 := hcontEval.continuousAt.tendsto.comp hNeumann
    convert h1 using 1
    ext n
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hex : ∃ p : ℕ, 0 < ((Pᵀ) ^ p *ᵥ lam) i := by
    by_contra hno
    push Not at hno
    have hps_nonpos : ∀ n : ℕ, ∑ k ∈ Finset.range n, ((Pᵀ) ^ k *ᵥ lam) i ≤ 0 :=
      fun n => Finset.sum_nonpos fun k _ => hno k
    have hle0 : traffic lam P i ≤ 0 := le_of_tendsto' hlim_i hps_nonpos
    linarith [hB4.traffic_pos i]
  obtain ⟨p, hp⟩ := hex
  exact ⟨p, chain_of_pos lam P hB4.lam_nonneg hB4.P_nonneg p i hp⟩
