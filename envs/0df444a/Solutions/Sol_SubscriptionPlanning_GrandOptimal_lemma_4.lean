-- Prove2me | solution 1 for SubscriptionPlanning.GrandOptimal.lemma_4
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:46:23.632977+00:00
-- url     : https://prove2.me/submissions/bfb27d29-04d3-46cf-9adc-65e9446d5c05

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

open MeasureTheory SubscriptionPlanning.GrandOptimal

namespace SubPlanL4Dis

universe u

/-- Three user types, one item, a single sample point. Values `v = (1/2, 2, 2)`, outside option `0`,
usage rates `λ = (2, 1, 2)`, masses `q = (1/2, 1/4, 1/4)`, horizon `T = 1`. -/
noncomputable def M0 : Model 3 1 PUnit.{u + 1} where
  P := Measure.dirac PUnit.unit
  V := fun i _ _ => ![(1 / 2 : ℝ), 2, 2] i
  V0 := fun _ => 0
  q := ![1 / 2, 1 / 4, 1 / 4]
  lam := ![2, 1, 2]
  T := 1

def r0 : Fin 1 → ℝ := fun _ => 1

theorem M0_valid : (M0.{u}).Valid where
  isProb := by unfold M0; infer_instance
  measV := fun _ _ => measurable_const
  measV0 := measurable_const
  intV := fun _ _ => by unfold M0; exact integrable_const _
  intV0 := by unfold M0; exact integrable_const _
  q_nonneg := by intro i; fin_cases i <;> simp [M0] <;> norm_num
  q_sum := by simp [M0, Fin.sum_univ_three]; norm_num
  lam_pos := by intro i; fin_cases i <;> simp [M0]
  T_pos := by simp [M0]

theorem best_eq (i : Fin 3) (S : Finset (Fin 1)) (ω : PUnit.{u + 1}) :
    best M0.{u} i S r0 ω = max 0 (util M0.{u} i S r0 ω ((0 : Fin 1) : WithBot (Fin 1))) := by
  unfold best
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun o _ => ?_)
    induction o using WithBot.recBotCoe with
    | bot => exact le_trans (le_of_eq (by simp [util, M0])) (le_max_left _ _)
    | coe j =>
      have : j = 0 := Subsingleton.elim _ _
      subst this
      exact le_max_right _ _
  · refine max_le ?_ ?_
    · exact le_trans (le_of_eq (by simp [util, M0])) (Finset.le_sup' (util M0 i S r0 ω) (Finset.mem_univ ⊥))
    · exact Finset.le_sup' (util M0 i S r0 ω) (Finset.mem_univ _)

theorem util_item (i : Fin 3) (S : Finset (Fin 1)) (ω : PUnit.{u + 1}) :
    util M0.{u} i S r0 ω ((0 : Fin 1) : WithBot (Fin 1)) =
      if (0 : Fin 1) ∈ S then ![(1 / 2 : ℝ), 2, 2] i else ![(1 / 2 : ℝ), 2, 2] i - 1 := by
  unfold util
  rw [WithBot.recBotCoe_coe]
  rfl

theorem fin1_cases (S : Finset (Fin 1)) : S = ∅ ∨ S = Finset.univ := by
  revert S; decide

theorem chosen_item_iff (i : Fin 3) (S : Finset (Fin 1)) (ω : PUnit.{u + 1}) :
    IsChosen M0.{u} i S r0 ω ((0 : Fin 1) : WithBot (Fin 1)) ↔
      0 < util M0.{u} i S r0 ω ((0 : Fin 1) : WithBot (Fin 1)) := by
  unfold IsChosen
  rw [best_eq]
  have hbot : util M0.{u} i S r0 ω ⊥ = 0 := by simp [util, M0]
  constructor
  · rintro ⟨_, h2⟩
    have := h2 ⊥ (WithBot.bot_lt_coe 0)
    rw [hbot] at this
    exact lt_of_lt_of_le this (by
      rcases le_total 0 (util M0 i S r0 ω ((0 : Fin 1) : WithBot (Fin 1))) with h | h
      · rw [max_eq_right h]
      · rw [max_eq_left h] at this; exact absurd this (lt_irrefl _))
  · intro h
    refine ⟨by rw [max_eq_right h.le], fun o' ho' => ?_⟩
    have : o' = ⊥ := by
      induction o' using WithBot.recBotCoe with
      | bot => rfl
      | coe j =>
        have : j = 0 := Subsingleton.elim _ _
        subst this
        exact absurd ho' (lt_irrefl _)
    subst this
    rw [hbot, max_eq_right h.le]
    exact h

theorem rentPaid_eq (i : Fin 3) (S : Finset (Fin 1)) (ω : PUnit.{u + 1}) :
    rentPaid M0.{u} i S r0 ω =
      if (0 : Fin 1) ∉ S ∧ 0 < util M0.{u} i S r0 ω ((0 : Fin 1) : WithBot (Fin 1)) then 1 else 0 := by
  unfold rentPaid
  rw [Fin.sum_univ_one]
  simp only [chosen_item_iff]
  rfl

theorem integral_eq (f : PUnit.{u + 1} → ℝ) : ∫ ω, f ω ∂(M0.{u}).P = f PUnit.unit := by
  show ∫ ω, f ω ∂(Measure.dirac PUnit.unit) = f PUnit.unit
  exact integral_dirac f PUnit.unit

theorem subGain_univ (i : Fin 3) :
    subGain M0.{u} i Finset.univ r0 = ![(1 / 2 : ℝ), 1, 1] i := by
  unfold subGain
  rw [integral_eq, integral_eq, best_eq, best_eq, util_item, util_item]
  fin_cases i <;> simp <;> norm_num

theorem subGain_empty (i : Fin 3) : subGain M0.{u} i ∅ r0 = 0 := by
  unfold subGain; ring

theorem rent_univ (i : Fin 3) : rent M0.{u} i Finset.univ r0 = 0 := by
  unfold rent
  rw [integral_eq, rentPaid_eq]
  simp

theorem rent_empty (i : Fin 3) : rent M0.{u} i ∅ r0 = ![(0 : ℝ), 1, 1] i := by
  unfold rent
  rw [integral_eq, rentPaid_eq, util_item]
  fin_cases i <;> simp <;> norm_num

theorem univ_ne : (Finset.univ : Finset (Fin 1)) ≠ ∅ := by decide

theorem subGain_cases (i : Fin 3) (S : Finset (Fin 1)) :
    subGain M0.{u} i S r0 = if S = ∅ then 0 else ![(1 / 2 : ℝ), 1, 1] i := by
  rcases fin1_cases S with h | h
  · subst h; simp [subGain_empty]
  · subst h; rw [subGain_univ, if_neg univ_ne]

theorem rent_cases (i : Fin 3) (S : Finset (Fin 1)) :
    rent M0.{u} i S r0 = if S = ∅ then ![(0 : ℝ), 1, 1] i else 0 := by
  rcases fin1_cases S with h | h
  · subst h; simp [rent_empty]
  · subst h; rw [rent_univ, if_neg univ_ne]

theorem cond2 : Condition2 M0.{u} r0 := by
  refine ⟨fun i S => ?_, fun i i' S => ?_⟩
  · rcases fin1_cases S with h | h
    · subst h; rw [subGain_empty]; simp
    · subst h; rw [rent_univ]; simp
  · rcases fin1_cases S with h | h
    · subst h; rw [subGain_empty, subGain_empty]; simp
    · subst h; ring

noncomputable def p0 : Finset (Fin 1) → ℝ := fun s => if s = ∅ then 0 else 1

def S0 : Fin 3 → Finset (Fin 1) := ![Finset.univ, ∅, Finset.univ]

theorem feasible_S0 : IsFeasible M0.{u} r0 p0 S0 := by
  refine ⟨by simp [p0], fun i S' => ?_⟩
  rw [subGain_cases, subGain_cases]
  have hT : M0.{u}.T = 1 := rfl
  rcases fin1_cases S' with h | h <;> subst h <;> fin_cases i <;>
    simp [S0, p0, M0, univ_ne] <;> norm_num

theorem optimal_S0 : IsOptimal M0.{u} r0 p0 S0 := by
  refine ⟨feasible_S0, fun p' S' hF => ?_⟩
  have hrev0 : revenue M0.{u} r0 p0 S0 = 1 := by
    unfold revenue
    simp only [Fin.sum_univ_three, rent_cases]
    simp [S0, p0, M0, univ_ne]
    norm_num
  rw [hrev0]
  -- incentive constraints between ∅ and univ
  have hIC : ∀ i, (S' i = Finset.univ → p' Finset.univ ≤ M0.{u}.lam i * ![(1 / 2 : ℝ), 1, 1] i) ∧
      (S' i = ∅ → M0.{u}.lam i * ![(1 / 2 : ℝ), 1, 1] i ≤ p' Finset.univ) := by
    intro i
    have hT : M0.{u}.T = 1 := rfl
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hF.2 i ∅
      rw [h, subGain_empty, subGain_univ, hF.1, hT] at this
      linarith
    · have := hF.2 i Finset.univ
      rw [h, subGain_empty, subGain_univ, hF.1, hT] at this
      linarith
  unfold revenue
  simp only [Fin.sum_univ_three, rent_cases]
  have h0 := hIC 0
  have h1 := hIC 1
  have h2 := hIC 2
  simp only [M0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 ⊢
  rcases fin1_cases (S' 0) with a | a <;> rcases fin1_cases (S' 1) with b | b <;>
    rcases fin1_cases (S' 2) with c | c <;>
    simp only [a, b, c, hF.1, if_true, univ_ne, if_false] at h0 h1 h2 ⊢ <;>
    norm_num at h0 h1 h2 ⊢ <;> linarith

theorem M0_q_pos : ∀ i, 0 < (M0.{u}).q i := by intro i; fin_cases i <;> simp [M0] <;> norm_num

theorem M0_sort : Monotone (fun i : Fin 3 => (M0.{u}).lam i * subGain M0.{u} i Finset.univ r0) := by
  intro a b hab
  simp only [subGain_univ]
  fin_cases a <;> fin_cases b <;> simp [M0] at hab ⊢ <;> norm_num at hab ⊢

theorem M0_ne : ¬ ((M0.{u}).lam 2 * (M0.{u}).T * subGain M0.{u} 2 (S0 2) r0 - p0 (S0 2) =
      (M0.{u}).lam 2 * (M0.{u}).T * subGain M0.{u} 2 (S0 1) r0 - p0 (S0 1)) := by
  rw [subGain_cases, subGain_cases]
  simp [S0, p0, M0, univ_ne]
  norm_num

end SubPlanL4Dis

open SubPlanL4Dis in
theorem solution : ¬ (∀ {n m : ℕ} {Ω : Type} [MeasurableSpace Ω] (M : SubscriptionPlanning.GrandOptimal.Model n m Ω)
    (hM : M.Valid) (hq : ∀ i, 0 < M.q i) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hC : SubscriptionPlanning.GrandOptimal.Condition2 M r) (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m))
    (hopt : SubscriptionPlanning.GrandOptimal.IsOptimal M r p S)
    (hsort : Monotone (fun i : Fin n => M.lam i * SubscriptionPlanning.GrandOptimal.subGain M i Finset.univ r))
    (i : Fin n) (hi : 0 < i.val),
    M.lam i * M.T * SubscriptionPlanning.GrandOptimal.subGain M i (S i) r - p (S i) =
      M.lam i * M.T * SubscriptionPlanning.GrandOptimal.subGain M i (S ⟨i.val - 1, by omega⟩) r -
        p (S ⟨i.val - 1, by omega⟩)) := by
  intro h
  exact M0_ne (h M0 M0_valid M0_q_pos.{0} r0 (fun _ => by simp [r0]) cond2 p0 S0 optimal_S0 M0_sort 2
    (by decide))
