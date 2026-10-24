-- Prove2me | solution 1 for PandoraBO.Private20261023.gittins_policy_mixture
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:50:44.951174+00:00
-- url     : https://prove2.me/submissions/262013e0-ebdb-42b3-951f-bff0da8ff392

import Theorems.Thm_PandoraBO_Private20261023_policy_terminal_measurable_integrable
import Theorems.Thm_PandoraBO_Private20261023_uniform_seed_mixture_integral
import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_reservation_index_exists_unique
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
An explicit mixture of two policies uses the seed interval [0,a] to select
the first policy and rescales it to [0,1]; the remaining interval selects and
rescales the second. This file constructs the measurable policy, proves its
pathwise coupling to both component policies, and preserves Gittins choices.
The expectation identity is a separate change-of-variables obligation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace PandoraBO.Private20261023.Mixing

def mixture {n : ℕ} (a : ℝ) (π ρ : Policy n) : Policy n where
  first := fun u => if u ≤ a then π.first (u / a) else ρ.first ((u - a) / (1 - a))
  first_measurable := Measurable.ite measurableSet_Iic
    (π.first_measurable.comp (measurable_id.div_const a))
    (ρ.first_measurable.comp ((measurable_id.sub_const a).div_const (1 - a)))
  next := fun p => if p.2 ≤ a then π.next (p.1, p.2 / a)
    else ρ.next (p.1, (p.2 - a) / (1 - a))
  next_measurable := Measurable.ite (measurableSet_le measurable_snd measurable_const)
    (π.next_measurable.comp (measurable_fst.prodMk (measurable_snd.div_const a)))
    (ρ.next_measurable.comp
      (measurable_fst.prodMk ((measurable_snd.sub_const a).div_const (1 - a))))
  next_unopened := by
    intro h u i hi
    by_cases hu : u ≤ a
    · exact π.next_unopened h (u / a) i (by simpa only [if_pos hu] using hi)
    · exact ρ.next_unopened h ((u - a) / (1 - a)) i
        (by simpa only [if_neg hu] using hi)

theorem first_left {n : ℕ} (a : ℝ) (π ρ : Policy n) (u : ℝ) (hu : u ≤ a) :
    (mixture a π ρ).first u = π.first (u / a) := if_pos hu

theorem first_right {n : ℕ} (a : ℝ) (π ρ : Policy n) (u : ℝ) (hu : ¬ u ≤ a) :
    (mixture a π ρ).first u = ρ.first ((u - a) / (1 - a)) := if_neg hu

theorem next_left {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (h : History n) (u : ℝ) (hu : u ≤ a) :
    (mixture a π ρ).next (h, u) = π.next (h, u / a) := if_pos hu

theorem next_right {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (h : History n) (u : ℝ) (hu : ¬ u ≤ a) :
    (mixture a π ρ).next (h, u) = ρ.next (h, (u - a) / (1 - a)) := if_neg hu

theorem rollout_left {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (r : Box n → ℝ) (u : ℝ) (hu : u ≤ a) (fuel step : ℕ) (h : History n) :
    rolloutAux (mixture a π ρ) (r, u) fuel step h =
      rolloutAux π (r, u / a) fuel step h := by
  induction fuel generalizing step h with
  | zero => rfl
  | succ fuel ih =>
      simp only [rolloutAux, next_left a π ρ h u hu]
      cases hd : π.next (h, u / a) with
      | none => rfl
      | some i =>
          by_cases hs : step < n + 1
          · simp only [dif_pos hs]
            exact ih (step + 1) (Function.update h ⟨step, hs⟩ (true, i, r i))
          · simp only [dif_neg hs]

theorem rollout_right {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (r : Box n → ℝ) (u : ℝ) (hu : ¬ u ≤ a) (fuel step : ℕ) (h : History n) :
    rolloutAux (mixture a π ρ) (r, u) fuel step h =
      rolloutAux ρ (r, (u - a) / (1 - a)) fuel step h := by
  induction fuel generalizing step h with
  | zero => rfl
  | succ fuel ih =>
      simp only [rolloutAux, next_right a π ρ h u hu]
      cases hd : ρ.next (h, (u - a) / (1 - a)) with
      | none => rfl
      | some i =>
          by_cases hs : step < n + 1
          · simp only [dif_pos hs]
            exact ih (step + 1) (Function.update h ⟨step, hs⟩ (true, i, r i))
          · simp only [dif_neg hs]

theorem initial_left {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (r : Box n → ℝ) (u : ℝ) (hu : u ≤ a) :
    initialHistory (mixture a π ρ) (r, u) = initialHistory π (r, u / a) := by
  funext k
  simp only [initialHistory, first_left a π ρ u hu]

theorem initial_right {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (r : Box n → ℝ) (u : ℝ) (hu : ¬ u ≤ a) :
    initialHistory (mixture a π ρ) (r, u) =
      initialHistory ρ (r, (u - a) / (1 - a)) := by
  funext k
  simp only [initialHistory, first_right a π ρ u hu]

theorem terminal_left {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (r : Box n → ℝ) (u : ℝ) (hu : u ≤ a) :
    terminalHistory (mixture a π ρ) (r, u) = terminalHistory π (r, u / a) := by
  unfold terminalHistory
  rw [initial_left a π ρ r u hu, rollout_left a π ρ r u hu]

theorem terminal_right {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (r : Box n → ℝ) (u : ℝ) (hu : ¬ u ≤ a) :
    terminalHistory (mixture a π ρ) (r, u) =
      terminalHistory ρ (r, (u - a) / (1 - a)) := by
  unfold terminalHistory
  rw [initial_right a π ρ r u hu, rollout_right a π ρ r u hu]

theorem terminalReward_mixture {n : ℕ} (a : ℝ) (π ρ : Policy n)
    (r : Box n → ℝ) (u : ℝ) :
    terminalReward (mixture a π ρ) (r, u) =
      if u ≤ a then terminalReward π (r, u / a)
      else terminalReward ρ (r, (u - a) / (1 - a)) := by
  by_cases hu : u ≤ a
  · simp only [if_pos hu, terminalReward, terminal_left a π ρ r u hu]
  · simp only [if_neg hu, terminalReward, terminal_right a π ρ r u hu]

theorem terminalCost_mixture {n : ℕ} (M : Instance n) (a : ℝ) (π ρ : Policy n)
    (r : Box n → ℝ) (u : ℝ) :
    terminalCost M (mixture a π ρ) (r, u) =
      if u ≤ a then terminalCost M π (r, u / a)
      else terminalCost M ρ (r, (u - a) / (1 - a)) := by
  by_cases hu : u ≤ a
  · simp only [if_pos hu, terminalCost, terminal_left a π ρ r u hu]
  · simp only [if_neg hu, terminalCost, terminal_right a π ρ r u hu]

theorem isGittinsPolicy_mixture {n : ℕ} (M : Instance n) (multiplier a : ℝ)
    (hpos : 0 < multiplier) (π ρ : Policy n)
    (hπ : isGittinsPolicy M multiplier π) (hρ : isGittinsPolicy M multiplier ρ) :
    isGittinsPolicy M multiplier (mixture a π ρ) := by
  obtain ⟨zπ, hzπ, hfirstπ, hnextπ⟩ := hπ
  obtain ⟨zρ, hzρ, hfirstρ, hnextρ⟩ := hρ
  have heq : zρ = zπ := by
    funext i
    obtain ⟨z, _hz, huniq⟩ :=
      PandoraBO.Private20261023.reservation_index_exists_unique M multiplier hpos i
    exact (huniq (zρ i) (hzρ i)).trans (huniq (zπ i) (hzπ i)).symm
  subst zρ
  refine ⟨zπ, hzπ, ?_, ?_⟩
  · intro u i
    by_cases hu : u ≤ a
    · simpa only [first_left a π ρ u hu] using hfirstπ (u / a) i
    · simpa only [first_right a π ρ u hu] using hfirstρ ((u - a) / (1 - a)) i
  · intro h u hh
    by_cases hu : u ≤ a
    · simpa only [next_left a π ρ h u hu] using hnextπ h (u / a) hh
    · simpa only [next_right a π ρ h u hu] using
        hnextρ h ((u - a) / (1 - a)) hh

theorem isZeroGittinsPolicy_mixture {n : ℕ} (M : Instance n) (a : ℝ)
    (π ρ : Policy n) (hπ : isZeroGittinsPolicy M π) (hρ : isZeroGittinsPolicy M ρ) :
    isZeroGittinsPolicy M (mixture a π ρ) := by
  constructor
  · intro u i
    by_cases hu : u ≤ a
    · simpa only [first_left a π ρ u hu] using hπ.1 (u / a) i
    · simpa only [first_right a π ρ u hu] using hρ.1 ((u - a) / (1 - a)) i
  · intro h u hh
    by_cases hu : u ≤ a
    · simpa only [next_left a π ρ h u hu] using hπ.2 h (u / a) hh
    · simpa only [next_right a π ρ h u hu] using hρ.2 h ((u - a) / (1 - a)) hh

end PandoraBO.Private20261023.Mixing


set_option autoImplicit false

noncomputable section

open MeasureTheory PandoraBO

namespace PandoraBO.Private20261023.Mixing

theorem expected_mixture {n : ℕ} (M : Instance n) (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (π ρ : Policy n) :
    expectedCost M (mixture a π ρ) =
        a * expectedCost M π + (1 - a) * expectedCost M ρ ∧
    expectedReward M (mixture a π ρ) =
        a * expectedReward M π + (1 - a) * expectedReward M ρ := by
  letI : ∀ i, IsProbabilityMeasure (M.law i) := M.law_probability
  have hπ := PandoraBO.Private20261023.policy_terminal_measurable_integrable M π
  have hρ := PandoraBO.Private20261023.policy_terminal_measurable_integrable M ρ
  have hσ := PandoraBO.Private20261023.policy_terminal_measurable_integrable M (mixture a π ρ)
  constructor
  · exact PandoraBO.Private20261023.uniform_seed_mixture_integral
      (Measure.pi M.law) a ha0 ha1 (terminalCost M π) (terminalCost M ρ)
      (terminalCost M (mixture a π ρ)) (terminalCost_mixture M a π ρ)
      hπ.2.2.2 hρ.2.2.2 hσ.2.2.2
  · exact PandoraBO.Private20261023.uniform_seed_mixture_integral
      (Measure.pi M.law) a ha0 ha1 (terminalReward π) (terminalReward ρ)
      (terminalReward (mixture a π ρ)) (terminalReward_mixture a π ρ)
      hπ.2.2.1 hρ.2.2.1 hσ.2.2.1

end PandoraBO.Private20261023.Mixing

theorem solution {n : ℕ} (M : Instance n) (multiplier : ℝ)
    (hpos : 0 < multiplier) (π ρ : Policy n)
    (hπ : isGittinsPolicy M multiplier π) (hρ : isGittinsPolicy M multiplier ρ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ σ : Policy n, isGittinsPolicy M multiplier σ ∧
      expectedCost M σ = a * expectedCost M π + (1 - a) * expectedCost M ρ ∧
      expectedReward M σ = a * expectedReward M π + (1 - a) * expectedReward M ρ := by
  by_cases hzero : a = 0
  · subst a
    exact ⟨ρ, hρ, by simp, by simp⟩
  by_cases hone : a = 1
  · subst a
    exact ⟨π, hπ, by simp, by simp⟩
  have hstrict0 : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
  have hstrict1 : a < 1 := lt_of_le_of_ne ha1 hone
  refine ⟨PandoraBO.Private20261023.Mixing.mixture a π ρ,
    PandoraBO.Private20261023.Mixing.isGittinsPolicy_mixture M multiplier a hpos π ρ hπ hρ, ?_⟩
  exact PandoraBO.Private20261023.Mixing.expected_mixture M a hstrict0 hstrict1 π ρ
