-- Prove2me | solution 1 for WeightedMajority.Basic.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:50:32.232378+00:00
-- url     : https://prove2.me/submissions/00ffda6e-12b5-4236-a1ad-bec356986abc

import Mathlib
import Definitions.Def_WeightedMajority_Basic_IsWMRun

open WeightedMajority.Basic

/-- The per-mistake weight estimate used in the proof of Theorem 2.1. -/
theorem wm_step {n T : ℕ} (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (initial : Fin n → ℝ) (hinitial : ∀ i, 0 < initial i)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool)
    (hrun : IsWMRun β initial x label w prediction)
    (t : Fin T) (hmistake : prediction t ≠ label t) :
    totalWeight w (t.val + 1) ≤ ((1 + β) / 2) * totalWeight w t.val := by
  have htot : totalWeight w t.val = voteWeight x w t false + voteWeight x w t true := by
    unfold totalWeight voteWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases x t i <;> simp
  have hup : totalWeight w (t.val + 1) =
      voteWeight x w t (label t) + β * voteWeight x w t (!(label t)) := by
    unfold totalWeight voteWeight
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrun.update]
    cases hl : label t <;> cases hx : x t i <;> simp_all
  have hmajor : voteWeight x w t (label t) ≤ voteWeight x w t (!(label t)) := by
    cases hl : label t
    · by_contra h
      have hp := hrun.predict_zero t (by simpa [hl] using lt_of_not_ge h)
      exact hmistake (hp.trans hl.symm)
    · by_contra h
      have hp := hrun.predict_one t (by simpa [hl] using lt_of_not_ge h)
      exact hmistake (hp.trans hl.symm)
  rw [hup, htot]
  cases hl : label t <;> simp only [hl, Bool.not_false, Bool.not_true] at * <;> nlinarith





/-- The whole-sequence weight estimate preceding Theorem 2.1. -/
theorem wm_potential {n T : ℕ} (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (initial : Fin n → ℝ) (hinitial : ∀ i, 0 < initial i)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool)
    (hrun : IsWMRun β initial x label w prediction) :
    totalWeight w T ≤ totalWeight w 0 * ((1 + β) / 2) ^ mistakeCount prediction label := by
  classical
  let M : ℕ → Finset (Fin T) := fun k => Finset.univ.filter (fun t => t.val < k ∧ prediction t ≠ label t)
  have hnonneg : ∀ k, k ≤ T → ∀ i, 0 ≤ w k i := by
    intro k
    induction k with
    | zero =>
      intro hk i
      rw [hrun.initial_weight]
      exact (hinitial i).le
    | succ k ih =>
      intro hk i
      have hkt : k < T := by omega
      rw [hrun.update ⟨k, hkt⟩ i]
      split_ifs
      · exact mul_nonneg hβ₀ (ih (by omega) i)
      · exact ih (by omega) i
  have hb : 0 ≤ (1 + β) / 2 := by linarith
  have hind : ∀ k, k ≤ T → totalWeight w k ≤ totalWeight w 0 * ((1 + β) / 2) ^ (M k).card := by
    intro k
    induction k with
    | zero => simp [M]
    | succ k ih =>
      intro hk
      have hkt : k < T := by omega
      let t : Fin T := ⟨k, hkt⟩
      have hprev := ih (by omega)
      by_cases hm : prediction t ≠ label t
      · have hset : M (k+1) = insert t (M k) := by
          ext a
          simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨ha, hma⟩
            by_cases hak : a.val < k
            · exact Or.inr ⟨hak, hma⟩
            · left; apply Fin.ext; dsimp [t]; omega
          · rintro (rfl | ⟨ha, hma⟩)
            · exact ⟨by dsimp [t]; omega, hm⟩
            · exact ⟨by omega, hma⟩
        have hnot : t ∉ M k := by simp [M, t]
        rw [hset, Finset.card_insert_of_notMem hnot, pow_succ]
        have hs := wm_step β hβ₀ hβ₁ initial hinitial x label w prediction hrun t hm
        change totalWeight w (k+1) ≤ _ at hs
        nlinarith [mul_le_mul_of_nonneg_left hprev hb]
      · have hset : M (k+1) = M k := by
          ext a
          simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨ha, hma⟩
            have hak : a.val < k := by
              by_contra hh
              have he : a = t := by apply Fin.ext; dsimp [t]; omega
              exact hm (he ▸ hma)
            exact ⟨hak, hma⟩
          · rintro ⟨ha, hma⟩; exact ⟨by omega, hma⟩
        have hw : totalWeight w (k+1) = totalWeight w k := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [t, hm] using hrun.update t i
        rw [hset, hw]
        exact hprev
  have hMT : M T = Finset.univ.filter (fun t => prediction t ≠ label t) := by
    ext t
    simp [M, t.isLt]
  simpa [hMT, mistakeCount] using hind T le_rfl






/-- Littlestone and Warmuth's Theorem 2.1. -/
theorem solution {n T : ℕ} (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (initial : Fin n → ℝ) (hinitial : ∀ i, 0 < initial i)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool)
    (hrun : IsWMRun β initial x label w prediction)
    (hfinal : 0 < totalWeight w T) :
    (mistakeCount prediction label : ℝ) ≤
      Real.log (totalWeight w 0 / totalWeight w T) /
        Real.log (2 / (1 + β)) := by
  have hp := wm_potential β hβ₀ hβ₁ initial hinitial x label w prediction hrun
  have hq : 0 < (1 + β) / 2 := by linarith
  have hq1 : (1 + β) / 2 < 1 := by linarith
  have h0 : 0 < totalWeight w 0 := by
    by_contra hh
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) (pow_nonneg hq.le (mistakeCount prediction label))
    linarith
  have hl := Real.log_le_log hfinal hp
  rw [Real.log_mul h0.ne' (pow_pos hq _).ne', Real.log_pow] at hl
  have hr : Real.log (totalWeight w 0 / totalWeight w T) =
      Real.log (totalWeight w 0) - Real.log (totalWeight w T) :=
    Real.log_div h0.ne' hfinal.ne'
  have hd : Real.log (2 / (1 + β)) = -Real.log ((1 + β) / 2) := by
    have he : (2 : ℝ) / (1 + β) = ((1 + β) / 2)⁻¹ := by
      field_simp
    rw [he, Real.log_inv]
  have hdpos : 0 < Real.log (2 / (1 + β)) := by
    rw [hd]
    have hh := Real.log_neg hq hq1
    linarith
  rw [le_div_iff₀ hdpos, hr, hd]
  nlinarith


#print axioms solution

