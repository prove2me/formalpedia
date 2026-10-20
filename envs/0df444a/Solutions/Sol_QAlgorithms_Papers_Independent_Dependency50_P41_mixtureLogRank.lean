-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P41.mixtureLogRank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:50:59.617555+00:00
-- url     : https://prove2.me/submissions/f20401a8-9fff-4de7-8d40-4eaeb5ac6735

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma g52a_rank_add {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma g52a_rank_smul {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ) (A : Matrix n n ℂ) :
    (c • A).rank ≤ A.rank := by
  have : c • A = (c • (1 : Matrix n n ℂ)) * A := by rw [Matrix.smul_mul, Matrix.one_mul]
  rw [this]
  exact Matrix.rank_mul_le_right _ _

lemma g52a_rank_sum {n ι : Type*} [Fintype n] (s : Finset ι) (M : ι → Matrix n n ℂ) :
    (∑ j ∈ s, M j).rank ≤ ∑ j ∈ s, (M j).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (g52a_rank_add _ _).trans (Nat.add_le_add_left ih _)

/-- arXiv:1108.5357v3, PDF p.20, Lemma 26, (A2).
No normalization of the positive operators or coefficients is needed for this rank bound. -/
theorem solution {A : Type*} [Fintype A] [Nonempty A]
    (N : ℕ) (hN : 0 < N) (p : Fin N → ℝ) (rho : Fin N → Op A)
    (hrho : ∀ j, (rho j).PosSemidef)
    (hmix : (∑ j, (p j : ℂ) • rho j).PosSemidef) :
    logRank (∑ j, (p j : ℂ) • rho j) ≤
      (⨆ j, logRank (rho j)) + (Real.logb 2 (N : ℝ) : EReal) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => (rho j).rank)
    Finset.univ_nonempty
  have hbound : (∑ j, (p j : ℂ) • rho j).rank ≤ N * (rho j0).rank := by
    refine (g52a_rank_sum _ _).trans ?_
    calc ∑ j, ((p j : ℂ) • rho j).rank ≤ ∑ _j : Fin N, (rho j0).rank :=
          Finset.sum_le_sum fun j _ => (g52a_rank_smul _ _).trans (hj0 j (Finset.mem_univ _))
      _ = N * (rho j0).rank := by simp
  unfold logRank logExtended
  set R := (∑ j, (p j : ℂ) • rho j).rank with hR
  by_cases h0 : (R : ℝ) ≤ 0
  · rw [if_pos h0]; exact bot_le
  · rw [if_neg h0]
    push_neg at h0
    have hR1 : 1 ≤ R := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro h; rw [h] at h0; simp at h0))
    have hr0 : 1 ≤ (rho j0).rank := by
      by_contra h
      push_neg at h
      have : (rho j0).rank = 0 := by omega
      rw [this, mul_zero] at hbound; omega
    have hr0' : ¬ (((rho j0).rank : ℝ) ≤ 0) := by
      push_neg; exact_mod_cast hr0
    have hle : (if (((rho j0).rank : ℕ) : ℝ) ≤ 0 then (⊥ : EReal)
        else ((Real.logb 2 ((rho j0).rank : ℝ) : ℝ) : EReal)) ≤
        ⨆ j, (if (((rho j).rank : ℕ) : ℝ) ≤ 0 then (⊥ : EReal)
          else ((Real.logb 2 ((rho j).rank : ℝ) : ℝ) : EReal)) :=
      le_iSup (fun j => (if (((rho j).rank : ℕ) : ℝ) ≤ 0 then (⊥ : EReal)
          else ((Real.logb 2 ((rho j).rank : ℝ) : ℝ) : EReal))) j0
    rw [if_neg hr0'] at hle
    refine le_trans ?_ (add_le_add hle le_rfl)
    have hr0pos : (0 : ℝ) < ((rho j0).rank : ℝ) := by exact_mod_cast hr0
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, ← Real.logb_mul hr0pos.ne' hNpos.ne']
    apply Real.logb_le_logb_of_le (by norm_num) h0
    have : (R : ℝ) ≤ (N : ℝ) * ((rho j0).rank : ℝ) := by exact_mod_cast hbound
    linarith


end

