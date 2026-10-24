-- Prove2me | solution 1 for OutpatientWalkIn.SmallCap.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:35:17.799596+00:00
-- url     : https://prove2.me/submissions/747d12b5-33c9-4405-8e88-1904184d291f

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Definitions.Def_OutpatientWalkIn_SmallCap_Setting
import Theorems.Thm_OutpatientWalkIn_SmallCap_proposition_1_obs_exists
import Theorems.Thm_OutpatientWalkIn_SmallCap_lemma_E_5_1
import Theorems.Thm_OutpatientWalkIn_SmallCap_thm2_proof_rate_bounds

open OutpatientWalkIn.SmallCap

theorem solution (M : Model) (hM : M.Standing) (hμ : M.mu ≤ Real.sqrt (M.lam * M.CD / (2 * M.R)))
    (μS : ℝ) (hμS : μS ∈ Set.Ico 0 M.mu) (u : UnobsStrategy) (hu : M.IsUnobsEq μS u) :
    ∃ μS' ∈ Set.Ico 0 M.mu, (∃ e : ObsStrategy, M.IsObsEq μS' e) ∧
      ∀ e : ObsStrategy, M.IsObsEq μS' e → M.obsCost μS' e ≤ M.unobsCost μS u := by
  refine ⟨μS, hμS, proposition_1_obs_exists M hM μS hμS, fun e he => ?_⟩
  apply lemma_E_5_1 M hM μS hμS u hu e he
  have hlam := hM.lam_pos
  have hR := hM.R_pos
  have hCD := hM.CD_pos
  rcases eq_or_lt_of_le hμS.1 with h0 | hpos
  · have hS : u.lamS = 0 := hu.unavailable h0.symm
    rw [hS, ← h0]; unfold blockProb; simp
  · -- λ/(1+λ/μS) ≤ λ(1-π(d̄))
    have hdb : 0 ≤ dbar μS u.lamS := by
      unfold dbar
      have := hu.stable hpos
      apply div_nonneg hu.lamS_nonneg
      have : 0 < μS - u.lamS := by linarith
      positivity
    have hb := (thm2_proof_rate_bounds M.lam hlam (dbar μS u.lamS) hdb μS hpos).1
    refine le_trans ?_ hb
    -- need u.lamS ≤ λ μS/(μS+λ)
    have hmu2 : 2 * M.R * μS ^ 2 ≤ M.lam * M.CD := by
      have h1 : μS ≤ Real.sqrt (M.lam * M.CD / (2 * M.R)) := le_trans hμS.2.le hμ
      have h2 : μS ^ 2 ≤ M.lam * M.CD / (2 * M.R) := by
        have := Real.sq_sqrt (show 0 ≤ M.lam * M.CD / (2 * M.R) by positivity)
        nlinarith [Real.sqrt_nonneg (M.lam * M.CD / (2 * M.R))]
      rw [le_div_iff₀ (by positivity)] at h2
      linarith
    have heq : M.lam / (1 + M.lam / μS) = M.lam * μS / (μS + M.lam) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    rcases eq_or_lt_of_le hu.lamS_nonneg with hz | hz
    · rw [← hz, zero_mul]; positivity
    · have hst := hu.stable hpos
      have hs := (hu.sched_best hz).2
      unfold Model.u1S dbar at hs
      have hd : 0 < μS - u.lamS := by linarith
      have h3 : M.CD * (u.lamS / (2 * μS * (μS - u.lamS))) ≤ M.R := by linarith
      rw [mul_div_assoc', div_le_iff₀ (by positivity)] at h3
      -- CD lamS ≤ 2R μS (μS - lamS)
      have h4 : u.lamS * (M.CD + 2 * M.R * μS) ≤ 2 * M.R * μS ^ 2 := by nlinarith
      have h5 : 0 < M.CD + 2 * M.R * μS := by positivity
      have h6 : (M.lam * μS - u.lamS * (μS + M.lam)) * (M.CD + 2 * M.R * μS) ≥ 0 := by
        nlinarith [mul_le_mul_of_nonneg_right h4 (show 0 ≤ μS + M.lam by positivity),
          mul_le_mul_of_nonneg_left hmu2 hpos.le]
      nlinarith [(mul_nonneg_iff_of_pos_right h5).1 h6]
