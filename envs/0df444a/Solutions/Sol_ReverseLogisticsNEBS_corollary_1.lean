-- Prove2me | solution 1 for ReverseLogisticsNEBS.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:28:37.429744+00:00
-- url     : https://prove2.me/submissions/7f4413c1-b0eb-4a55-b6cd-f38bccee746e

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Sched

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ReverseLogisticsNEBS

namespace ReverseLogisticsNEBS.Cor1Proof

theorem gamma_anti {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model N Ω) (hM : M.Standing) (t : ℕ) (ω : Ω)
    {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    M.gamma t ω y₂ ≤ M.gamma t ω y₁ := by
  haveI : IsMarkovKernel (M.κ t) := hM.markov t
  have hint : ∀ y : ℝ, Integrable (fun z : ℝ × Ω => max (z.1 - y) 0) (M.κ t ω) := by
    intro y
    have hsub : Integrable (fun z : ℝ × Ω => z.1 - y) (M.κ t ω) :=
      (hM.demand_integrable t ω).sub (integrable_const y)
    have heq : (fun z : ℝ × Ω => max (z.1 - y) 0) =
        fun z => (z.1 - y + |z.1 - y|) / 2 := by
      ext z
      rcases le_total (z.1 - y) 0 with h | h
      · rw [max_eq_right h, abs_of_nonpos h]; ring
      · rw [max_eq_left h, abs_of_nonneg h]; ring
    rw [heq]
    exact (hsub.add hsub.abs).div_const 2
  have hmono : ∫ z, max (z.1 - y₂) 0 ∂(M.κ t ω) ≤ ∫ z, max (z.1 - y₁) 0 ∂(M.κ t ω) :=
    integral_mono (hint y₂) (hint y₁) (fun z => max_le_max_right 0 (by linarith))
  have hH0 : 0 ≤ M.Hext 0 := by
    unfold Model.Hext
    split_ifs with hN
    · exact hM.H_nonneg _
    · exact le_rfl
  unfold Model.gamma
  linarith [mul_le_mul_of_nonneg_left hmono (add_nonneg hM.p_nonneg hH0)]

end ReverseLogisticsNEBS.Cor1Proof

open ReverseLogisticsNEBS.Cor1Proof in
theorem solution {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (t : ℕ)
    (F : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (y : Fin N → ℝ) (hy : Monotone y) (s : Sched N)
    (hs : M.IsOptimalDecision t F (Sched.FeasRelax y) ω s) :
    ∀ j, 0 < M.cE j → 0 < M.cR j → Sched.UnidirAt y s j := by
  obtain ⟨⟨⟨hyYE, hYEm, hYR0, hYEYR, hYRYE, hYRY⟩, hYYR⟩, hint, hopt⟩ := hs
  intro j hcEj hcRj
  unfold Sched.UnidirAt
  by_cases hYRj : s.YR j = s.YE j
  · exact Or.inr hYRj
  · left
    have hYRltYE : s.YR j < s.YE j := lt_of_le_of_ne (hYRYE j) hYRj
    -- Step 1: lowering s.YE j to max (y j) (s.YR j) forces s.YE j = y j
    have hYEj : s.YE j = y j := by
      by_contra hne
      have hyltYE : y j < s.YE j := lt_of_le_of_ne (hyYE j) (Ne.symm hne)
      set v := max (y j) (s.YR j) with hvdef
      have hvlt : v < s.YE j := max_lt hyltYE hYRltYE
      let s' : Sched N := { s with YE := Function.update s.YE j v }
      have hfeas' : Sched.FeasRelax y s' := by
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, hYRY⟩, hYYR⟩
        · intro k
          by_cases hk : k = j
          · subst hk; simp [s', v]
          · simp [s', hk, hyYE k]
        · intro i k hik
          have hki : k ≠ i := by intro h; subst h; omega
          by_cases hi : i = j
          · subst hi
            have hk_ne : k ≠ i := hki
            simp only [s', Function.update_self, Function.update_of_ne hk_ne]
            exact (hYEYR i k hik).trans (le_max_right _ _)
          · by_cases hk : k = j
            · subst hk
              simp only [s', Function.update_of_ne hi, Function.update_self]
              exact hvlt.le.trans (hYEm i k hik)
            · simp [s', hi, hk, hYEm i k hik]
        · intro k hk0
          by_cases hk : k = j
          · subst hk
            simp only [s', Function.update_self, negPartMin]
            exact (min_le_min_right 0 hvlt.le).trans (hYR0 k hk0)
          · simp [s', hk, hYR0 k hk0]
        · intro i k hik
          by_cases hk : k = j
          · subst hk
            simp only [s', Function.update_self]
            exact hvlt.le.trans (hYEYR i k hik)
          · simp [s', hk, hYEYR i k hik]
        · intro k
          by_cases hk : k = j
          · subst hk; simp [s', v]
          · simp [s', hk, hYRYE k]
      have hint' : M.ContIntegrable t F ω s' := hint
      have hsum' : ∑ k, (M.cE k * s.YE k + M.c k * s.Y k - M.cR k * s.YR k) -
          ∑ k, (M.cE k * s'.YE k + M.c k * s'.Y k - M.cR k * s'.YR k) =
          M.cE j * (s.YE j - v) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
        · simp only [s', Function.update_self]; ring
        · intro k _ hkj; simp [s', hkj]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hlt' : M.stageObj t F ω s' < M.stageObj t F ω s := by
        unfold Model.stageObj Model.nextState
        have hpos : 0 < M.cE j * (s.YE j - v) := mul_pos hcEj (sub_pos.mpr hvlt)
        simp only [s'] at hsum' ⊢
        linarith
      linarith [hopt s' hfeas' hint']
    refine ⟨hYEj, ?_⟩
    -- Step 2: raising s.YR j to min (s.YE j) (s.Y j) forces s.Y j = s.YR j
    by_contra hneY
    have hYRltY : s.YR j < s.Y j := lt_of_le_of_ne (hYRY j) (Ne.symm hneY)
    set w := min (s.YE j) (s.Y j) with hwdef
    have hwgt : s.YR j < w := lt_min hYRltYE hYRltY
    let s'' : Sched N := { s with YR := Function.update s.YR j w }
    have hYRle : ∀ k, s.YR k ≤ s''.YR k := by
      intro k
      by_cases hk : k = j
      · subst hk; simp [s'', hwgt.le]
      · simp [s'', hk]
    have hfeas'' : Sched.FeasRelax y s'' := by
      refine ⟨⟨hyYE, hYEm, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro k hk0; exact (hYR0 k hk0).trans (hYRle k)
      · intro i k hik; exact (hYEYR i k hik).trans (hYRle i)
      · intro k
        by_cases hk : k = j
        · subst hk; simp [s'', w]
        · simp [s'', hk, hYRYE k]
      · intro k
        by_cases hk : k = j
        · subst hk; simp [s'', w]
        · simp [s'', hk, hYRY k]
      · intro i k hik; exact (hYYR i k hik).trans (hYRle i)
    have hint'' : M.ContIntegrable t F ω s'' := hint
    have hfirst : firstLoc s.YR ≤ firstLoc s''.YR := by
      unfold firstLoc
      split_ifs with hN
      · exact hYRle ⟨0, hN⟩
      · exact le_rfl
    have hgam'' : M.gamma t ω (firstLoc s''.YR) ≤ M.gamma t ω (firstLoc s.YR) :=
      gamma_anti M hM t ω hfirst
    have hsum'' : ∑ k, (M.cE k * s.YE k + M.c k * s.Y k - M.cR k * s.YR k) -
        ∑ k, (M.cE k * s''.YE k + M.c k * s''.Y k - M.cR k * s''.YR k) =
        M.cR j * (w - s.YR j) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
      · simp only [s'', Function.update_self]; ring
      · intro k _ hkj; simp [s'', hkj]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hlt'' : M.stageObj t F ω s'' < M.stageObj t F ω s := by
      unfold Model.stageObj Model.nextState
      have hpos : 0 < M.cR j * (w - s.YR j) := mul_pos hcRj (sub_pos.mpr hwgt)
      linarith
    linarith [hopt s'' hfeas'' hint'']
