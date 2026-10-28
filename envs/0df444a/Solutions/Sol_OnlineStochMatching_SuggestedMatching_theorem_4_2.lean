-- Prove2me | solution 2 for OnlineStochMatching.SuggestedMatching.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T15:20:29.582865+00:00
-- url     : https://prove2.me/submissions/0528ee34-b4dd-4a78-95bb-d0d83f2de5a9

import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm
import Theorems.Thm_UniformCounting_uniformProbability_and
import Theorems.Thm_UniformCounting_uniformProbability_mono
import Theorems.Thm_OnlineStochMatching_SuggestedMatching_bounding_alg
import Theorems.Thm_OnlineStochMatching_SuggestedMatching_opt_bound
import Theorems.Thm_OnlineStochMatching_SuggestedMatching_tightness

set_option autoImplicit false
open OnlineStochMatching.SuggestedMatching

-- carved from submission 4a5e26af-423d-4e99-b667-4dcd719297c2, lines 1170-1258

theorem solution :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option A) (hlabel : IsLabelling inst M label),
        runProbability inst (fun ω =>
          (1 - Real.exp (-1)) * (optimum inst ω : ℝ) - ε * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ))) ∧
    (∀ (n : ℕ) (hn : 0 < n),
      let inst := completeInstance n hn
      ∀ (M : Finset (Fin n × Fin n)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option (Fin n)) (hlabel : IsLabelling inst M label),
        (∀ ω : Fin inst.n → inst.Copy, optimum inst ω = n) ∧
          expectedAlgorithm inst label =
            (n : ℝ) * (1 - (1 - 1 / (n : ℝ)) ^ n)) ∧
    Filter.Tendsto (fun n : ℕ => 1 - (1 - 1 / (n : ℝ)) ^ n)
      Filter.atTop (nhds (1 - Real.exp (-1))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ1, hδ1, N1, h1⟩ := OnlineStochMatching.SuggestedMatching.bounding_alg (ε / 2) (by positivity)
    obtain ⟨δ2, hδ2, N2, h2⟩ := OnlineStochMatching.SuggestedMatching.opt_bound (ε / 2) (by positivity)
    set δ' := min δ1 δ2 with hδ'
    have hδ'0 : 0 < δ' := lt_min hδ1 hδ2
    refine ⟨δ' / 2, by positivity, max (max N1 N2) ⌈2 / δ'⌉₊, ?_⟩
    intro A I _ _ inst hn M hM label hlabel
    have hnN1 : N1 ≤ inst.n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnN2 : N2 ≤ inst.n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hnN3 : ⌈2 / δ'⌉₊ ≤ inst.n := le_trans (le_max_right _ _) hn
    have hA := h1 A I inst hnN1 M hM label hlabel
    have hB := h2 A I inst hnN2 M hM
    have hAB : runProbability inst
          (fun ω => (1 - Real.exp (-1)) * (coveredAds M).card - (ε/2) * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) +
        runProbability inst
          (fun ω => (optimum inst ω : ℝ) ≤ (coveredAds M).card + (ε/2) * (inst.n : ℝ)) - 1 ≤
        runProbability inst (fun ω =>
          ((1 - Real.exp (-1)) * (coveredAds M).card - (ε/2) * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) ∧
          ((optimum inst ω : ℝ) ≤ (coveredAds M).card + (ε/2) * (inst.n : ℝ))) :=
      UniformCounting.uniformProbability_and _ _
    have hmono : runProbability inst (fun ω =>
          ((1 - Real.exp (-1)) * (coveredAds M).card - (ε/2) * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) ∧
          ((optimum inst ω : ℝ) ≤ (coveredAds M).card + (ε/2) * (inst.n : ℝ))) ≤
        runProbability inst (fun ω =>
          (1 - Real.exp (-1)) * (optimum inst ω : ℝ) - ε * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) :=
      UniformCounting.uniformProbability_mono (fun ω =>
      ((1 - Real.exp (-1)) * (coveredAds M).card - (ε/2) * (inst.n : ℝ) ≤ (algorithm inst label ω : ℝ)) ∧
      ((optimum inst ω : ℝ) ≤ (coveredAds M).card + (ε/2) * (inst.n : ℝ)))
      (fun ω => (1 - Real.exp (-1)) * (optimum inst ω : ℝ) - ε * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) (by
        intro ω ⟨hω1, hω2⟩
        have he : Real.exp (-1) > 0 := Real.exp_pos _
        have he1 : Real.exp (-1) ≤ 1 := by
          rw [Real.exp_le_one_iff]; norm_num
        have hn0 : (0:ℝ) ≤ inst.n := Nat.cast_nonneg _
        have hc : (0:ℝ) ≤ 1 - Real.exp (-1) := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hω2 hc, mul_nonneg hε.le hn0])
    have hnR : (0:ℝ) < inst.n := by exact_mod_cast inst.n_pos
    have hexp1 : Real.exp (-δ1 * inst.n) ≤ Real.exp (-δ' * inst.n) := by
      apply Real.exp_le_exp.mpr
      have : δ' ≤ δ1 := min_le_left _ _
      nlinarith
    have hexp2 : Real.exp (-δ2 * inst.n) ≤ Real.exp (-δ' * inst.n) := by
      apply Real.exp_le_exp.mpr
      have : δ' ≤ δ2 := min_le_right _ _
      nlinarith
    have hbig : (2:ℝ) ≤ Real.exp (δ' / 2 * inst.n) := by
      have h : 2 / δ' ≤ inst.n := (Nat.le_ceil _).trans (by exact_mod_cast hnN3)
      rw [div_le_iff₀ hδ'0] at h
      have := Real.add_one_le_exp (δ' / 2 * inst.n)
      nlinarith
    have hsplit : Real.exp (-δ' * inst.n) = Real.exp (-(δ' / 2) * inst.n) * Real.exp (-(δ' / 2 * inst.n)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hinv : Real.exp (-(δ' / 2 * inst.n)) * Real.exp (δ' / 2 * inst.n) = 1 := by
      rw [← Real.exp_add]; simp
    have hsmall : 2 * Real.exp (-(δ' / 2 * inst.n)) ≤ 1 := by
      have := Real.exp_pos (-(δ' / 2 * inst.n))
      nlinarith
    have hfin : 2 * Real.exp (-δ' * inst.n) ≤ Real.exp (-(δ' / 2) * inst.n) := by
      rw [hsplit]
      have := Real.exp_pos (-(δ' / 2) * inst.n)
      nlinarith
    show 1 - Real.exp (-(δ' / 2) * (inst.n : ℝ)) ≤ _
    simp only [ge_iff_le] at hA hB
    linarith
  · intro n hn inst M hM label hlabel
    exact OnlineStochMatching.SuggestedMatching.tightness n hn M hM label hlabel
  · have := Real.tendsto_one_add_div_pow_exp (-1)
    have h2 : Filter.Tendsto (fun n : ℕ => 1 - (1 + (-1) / (n:ℝ)) ^ n) Filter.atTop (nhds (1 - Real.exp (-1))) :=
      tendsto_const_nhds.sub this
    refine h2.congr (fun n => ?_)
    congr 2
    ring
