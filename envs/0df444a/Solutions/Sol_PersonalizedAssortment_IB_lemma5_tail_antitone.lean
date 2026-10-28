-- Prove2me | solution 1 for PersonalizedAssortment.IB.lemma5_tail_antitone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:14:22.291524+00:00
-- url     : https://prove2.me/submissions/7147f412-7c2f-4b78-89ef-1bcfe5d3c172

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction

open PersonalizedAssortment.IB in
theorem solution (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ)
    (hconc : ConcaveOn ℝ (Set.Icc 0 1) Ψ) (hdiff : DifferentiableOn ℝ Ψ (Set.Icc 0 1))
    (hdiff2 : DifferentiableOn ℝ (derivWithin Ψ (Set.Icc 0 1)) (Set.Icc 0 1))
    (a : ℝ) (ha : a ∈ Set.Ico 0 1) :
    AntitoneOn (fun C : ℝ => 1 / C + ∫ y in (a + 1 / C)..1, Ψ y) (Set.Ici (1 / (1 - a))) := by
  obtain ⟨ha0, ha1⟩ := ha
  have hpos : 0 < 1 - a := by linarith
  have hcont : ContinuousOn Ψ (Set.Icc 0 1) := hdiff.continuousOn
  have hle1 : ∀ y ∈ Set.Icc (0:ℝ) 1, Ψ y ≤ 1 := fun y hy => (hΨ.1 hy).2
  -- facts about C in the set
  have key : ∀ C : ℝ, 1 / (1 - a) ≤ C → 0 < C ∧ a + 1 / C ≤ 1 := by
    intro C hC
    have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
    refine ⟨hC0, ?_⟩
    have : 1 / C ≤ 1 - a := by
      rw [div_le_iff₀ hC0]
      rw [div_le_iff₀ hpos] at hC
      linarith
    linarith
  intro C1 h1 C2 h2 h12
  simp only [Set.mem_Ici] at h1 h2
  obtain ⟨c1pos, k1⟩ := key C1 h1
  obtain ⟨c2pos, k2⟩ := key C2 h2
  have hinv : 1 / C2 ≤ 1 / C1 := one_div_le_one_div_of_le c1pos h12
  have hinv2 : 0 < 1 / C2 := by positivity
  -- C1 ≤ C2 : want F C2 ≤ F C1
  show 1 / C2 + ∫ y in (a + 1 / C2)..1, Ψ y ≤ 1 / C1 + ∫ y in (a + 1 / C1)..1, Ψ y
  have hint : ∀ x y : ℝ, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
      IntervalIntegrable Ψ MeasureTheory.volume x y := fun x y hx hy =>
    (hcont.mono (Set.uIcc_subset_Icc hx hy)).intervalIntegrable
  have m1 : a + 1 / C1 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [one_div_pos.2 c1pos], k1⟩
  have m2 : a + 1 / C2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, k2⟩
  have m3 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have split := intervalIntegral.integral_add_adjacent_intervals
    (hint _ _ m2 m1) (hint _ _ m1 m3)
  have hmono : ∫ y in (a + 1 / C2)..(a + 1 / C1), Ψ y ≤ ∫ y in (a + 1 / C2)..(a + 1 / C1), (1:ℝ) := by
    apply intervalIntegral.integral_mono_on (by linarith) (hint _ _ m2 m1)
      (by simp)
    intro y hy
    exact hle1 y ⟨by linarith [hy.1, m2.1], by linarith [hy.2, m1.2]⟩
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hmono
  rw [← split]
  linarith
