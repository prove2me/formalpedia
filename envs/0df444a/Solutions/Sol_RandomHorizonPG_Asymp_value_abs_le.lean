-- Prove2me | solution 1 for RandomHorizonPG.Asymp.value_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:58:53.890126+00:00
-- url     : https://prove2.me/submissions/41b66262-0c90-4d9e-8d31-e031e17dff21

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

open FoundationsML.ReinforcementLearning

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR : ℝ) (hP : IsTransitionKernel P)
    (hγ : 0 < γ ∧ γ < 1) (hR : ∀ s a, |R s a| ≤ UR) (ν : S → A → ℝ) (hν : IsPolicy ν) :
    (∀ s a, |QFunction ν P R γ s a| ≤ UR / (1 - γ)) ∧
      ∀ s, |PolicyValue ν P R γ s| ≤ UR / (1 - γ) := by
  have hIT : ∀ s s', 0 ≤ InducedTransition ν P s s' := fun s s' =>
    Finset.sum_nonneg (fun a _ => mul_nonneg ((hν s).1 a) ((hP s a).1 s'))
  have hITsum : ∀ s, ∑ s', InducedTransition ν P s s' = 1 := by
    intro s
    unfold InducedTransition
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
    exact (hν s).2
  have hocc : ∀ s0 t, (∀ s', 0 ≤ OccupationDist ν P s0 t s') ∧
      ∑ s', OccupationDist ν P s0 t s' = 1 := by
    intro s0 t
    induction t with
    | zero =>
      refine ⟨fun s' => ?_, ?_⟩
      · simp only [OccupationDist]; split_ifs <;> norm_num
      · simp [OccupationDist]
    | succ k ih =>
      refine ⟨fun s' => ?_, ?_⟩
      · simp only [OccupationDist]
        exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (hIT s s'))
      · simp only [OccupationDist]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hITsum, mul_one]
        exact ih.2
  have hIR : ∀ s, |InducedReward ν R s| ≤ UR := by
    intro s
    unfold InducedReward
    calc |∑ a, ν s a * R s a| ≤ ∑ a, |ν s a * R s a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ν s a * UR := by
        apply Finset.sum_le_sum
        intro a _
        rw [abs_mul, abs_of_nonneg ((hν s).1 a)]
        exact mul_le_mul_of_nonneg_left (hR s a) ((hν s).1 a)
      _ = UR := by rw [← Finset.sum_mul, (hν s).2, one_mul]
  have hV : ∀ s, |PolicyValue ν P R γ s| ≤ UR / (1 - γ) := by
    intro s
    unfold PolicyValue
    have hterm : ∀ t, ‖γ ^ t * ∑ s', OccupationDist ν P s t s' * InducedReward ν R s'‖ ≤
        γ ^ t * UR := by
      intro t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ.1.le t)]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hγ.1.le t)
      calc |∑ s', OccupationDist ν P s t s' * InducedReward ν R s'|
          ≤ ∑ s', |OccupationDist ν P s t s' * InducedReward ν R s'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s', OccupationDist ν P s t s' * UR := by
            apply Finset.sum_le_sum
            intro s' _
            rw [abs_mul, abs_of_nonneg ((hocc s t).1 s')]
            exact mul_le_mul_of_nonneg_left (hIR s') ((hocc s t).1 s')
        _ = UR := by rw [← Finset.sum_mul, (hocc s t).2, one_mul]
    have hs : HasSum (fun t : ℕ => γ ^ t * UR) ((1 - γ)⁻¹ * UR) :=
      (hasSum_geometric_of_lt_one hγ.1.le hγ.2).mul_right UR
    have := tsum_of_norm_bounded hs hterm
    rw [Real.norm_eq_abs] at this
    rw [div_eq_inv_mul]
    exact this
  refine ⟨fun s a => ?_, hV⟩
  unfold QFunction
  have hsum : |∑ s', P s a s' * PolicyValue ν P R γ s'| ≤ UR / (1 - γ) := by
    calc |∑ s', P s a s' * PolicyValue ν P R γ s'|
        ≤ ∑ s', |P s a s' * PolicyValue ν P R γ s'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', P s a s' * (UR / (1 - γ)) := by
          apply Finset.sum_le_sum
          intro s' _
          rw [abs_mul, abs_of_nonneg ((hP s a).1 s')]
          exact mul_le_mul_of_nonneg_left (hV s') ((hP s a).1 s')
      _ = UR / (1 - γ) := by rw [← Finset.sum_mul, (hP s a).2, one_mul]
  have h1g : 0 < 1 - γ := by linarith [hγ.2]
  have hid : UR + γ * (UR / (1 - γ)) = UR / (1 - γ) := by
    field_simp
    ring
  calc |R s a + γ * ∑ s', P s a s' * PolicyValue ν P R γ s'|
      ≤ |R s a| + |γ * ∑ s', P s a s' * PolicyValue ν P R γ s'| := abs_add_le _ _
    _ ≤ UR + γ * (UR / (1 - γ)) := by
        rw [abs_mul, abs_of_pos hγ.1]
        have := mul_le_mul_of_nonneg_left hsum hγ.1.le
        linarith [hR s a]
    _ = UR / (1 - γ) := hid
