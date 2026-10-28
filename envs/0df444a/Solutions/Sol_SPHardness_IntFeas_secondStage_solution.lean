-- Prove2me | solution 1 for SPHardness.IntFeas.secondStage_solution
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:21:18.527568+00:00
-- url     : https://prove2.me/submissions/fdeaf8fd-5032-4d0b-8394-892680d7a7a7

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model

open SPHardness.IntFeas
open MeasureTheory

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (x : ℝ) (ξ : Fin n → ℝ) (hξ : ξ ∈ SPHardness.FixedRecourse.cube n) :
    (InPolytope A b ξ →
      (SecondStageSolvable A b x ξ ↔ ∑ i, max (ξ i) (1 - ξ i) ≤ x) ∧
      (SecondStageSolvable A b x ξ →
        secondStageValue A b x ξ = ∑ i, max (ξ i) (1 - ξ i)) ∧
      (∀ y lam, SecondStageFeasible A b x ξ y lam →
        ∑ i, y i = secondStageValue A b x ξ → ∀ i, y i = max (ξ i) (1 - ξ i))) ∧
    (¬ InPolytope A b ξ →
      (SecondStageSolvable A b x ξ ↔ 0 ≤ x) ∧
      (SecondStageSolvable A b x ξ → secondStageValue A b x ξ = 0) ∧
      (∀ y lam, SecondStageFeasible A b x ξ y lam →
        ∑ i, y i = secondStageValue A b x ξ → ∀ i, y i = 0)) := by
  have hξi : ∀ i, 0 ≤ ξ i ∧ ξ i ≤ 1 := fun i => hξ i (Set.mem_univ i)
  constructor
  · intro hP
    have hsl : ∀ r, 0 ≤ slack A b ξ r := fun r => by unfold slack; linarith [hP r]
    have low : ∀ y lam, SecondStageFeasible A b x ξ y lam → ∀ i, max (ξ i) (1 - ξ i) ≤ y i := by
      intro y lam hF i
      have hS : 0 ≤ ∑ r, slack A b ξ r * lam r :=
        Finset.sum_nonneg (fun r _ => mul_nonneg (hsl r) (hF.2.1 r))
      obtain ⟨h1, h2⟩ := hF.2.2.2 i
      exact max_le (by linarith) (by linarith)
    have lowS : ∀ y lam, SecondStageFeasible A b x ξ y lam → ∑ i, max (ξ i) (1 - ξ i) ≤ ∑ i, y i :=
      fun y lam hF => Finset.sum_le_sum (fun i _ => low y lam hF i)
    have wit : ∑ i, max (ξ i) (1 - ξ i) ≤ x →
        SecondStageFeasible A b x ξ (fun i => max (ξ i) (1 - ξ i)) 0 := by
      intro hx
      refine ⟨fun i => le_trans (hξi i).1 (le_max_left _ _), fun r => le_rfl, hx, fun i => ?_⟩
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
      exact ⟨le_max_left _ _, le_max_right _ _⟩
    have solv : SecondStageSolvable A b x ξ ↔ ∑ i, max (ξ i) (1 - ξ i) ≤ x := by
      constructor
      · rintro ⟨y, lam, hF⟩; exact le_trans (lowS y lam hF) hF.2.2.1
      · intro hx; exact ⟨_, _, wit hx⟩
    have val : SecondStageSolvable A b x ξ → secondStageValue A b x ξ = ∑ i, max (ξ i) (1 - ξ i) := by
      intro hs
      apply IsLeast.csInf_eq
      refine ⟨⟨_, _, wit (solv.mp hs), rfl⟩, ?_⟩
      rintro v ⟨y, lam, hF, rfl⟩
      exact lowS y lam hF
    refine ⟨solv, val, fun y lam hF hsum i => ?_⟩
    rw [val ⟨y, lam, hF⟩] at hsum
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => low y lam hF i)).mp hsum.symm i (Finset.mem_univ i)
    exact this.symm
  · intro hP
    unfold InPolytope at hP
    push_neg at hP
    obtain ⟨r, hr⟩ := hP
    have hsr : slack A b ξ r < 0 := by unfold slack; linarith
    have wit : 0 ≤ x → SecondStageFeasible A b x ξ 0 (Pi.single r (-(slack A b ξ r)⁻¹)) := by
      intro hx
      have hsum : ∑ r', slack A b ξ r' * (Pi.single r (-(slack A b ξ r)⁻¹) : Fin m → ℝ) r' = -1 := by
        rw [Finset.sum_eq_single r]
        · rw [Pi.single_eq_same, mul_neg, mul_inv_cancel₀ hsr.ne]
        · intro r' _ hne; simp [Pi.single_apply, hne]
        · intro h; exact absurd (Finset.mem_univ r) h
      refine ⟨fun i => le_rfl, fun r' => ?_, by simpa using hx, fun i => ?_⟩
      · by_cases h : r' = r
        · subst h; rw [Pi.single_eq_same]
          have : 0 < -(slack A b ξ r')⁻¹ := by
            rw [neg_pos]; exact inv_lt_zero.mpr hsr
          exact this.le
        · simp [Pi.single_apply, h]
      · rw [hsum]
        simp only [Pi.zero_apply]
        constructor <;> linarith [hξi i]
    have nonneg : ∀ y lam, SecondStageFeasible A b x ξ y lam → 0 ≤ ∑ i, y i :=
      fun y lam hF => Finset.sum_nonneg (fun i _ => hF.1 i)
    have solv : SecondStageSolvable A b x ξ ↔ 0 ≤ x := by
      constructor
      · rintro ⟨y, lam, hF⟩; exact le_trans (nonneg y lam hF) hF.2.2.1
      · intro hx; exact ⟨_, _, wit hx⟩
    have val : SecondStageSolvable A b x ξ → secondStageValue A b x ξ = 0 := by
      intro hs
      apply IsLeast.csInf_eq
      refine ⟨⟨_, _, wit (solv.mp hs), by simp⟩, ?_⟩
      rintro v ⟨y, lam, hF, rfl⟩
      exact nonneg y lam hF
    refine ⟨solv, val, fun y lam hF hsum i => ?_⟩
    rw [val ⟨y, lam, hF⟩] at hsum
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hF.1 i)).mp hsum i (Finset.mem_univ i)
