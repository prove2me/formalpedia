-- Prove2me | solution 1 for QuantumMaxCutEnergy.finite_repetition_expected_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T14:27:06.552728+00:00
-- url     : https://prove2.me/submissions/37f04419-fc5c-4efe-ad0a-1e58c90a6322

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace QuantumMaxCutEnergy.Sampling

theorem all_failure_card {Ω : Type*} [Fintype Ω]
    (bad : Ω → Prop) [DecidablePred bad] (k : ℕ) :
    (Finset.univ.filter (fun s : Fin k → Ω => ∀ i, bad (s i))).card =
      (Finset.univ.filter bad).card ^ k := by
  classical
  have hset : Finset.univ.filter (fun s : Fin k → Ω => ∀ i, bad (s i)) =
      Fintype.piFinset (fun _ : Fin k => Finset.univ.filter bad) := by
    ext s
    simp
  rw [hset, Fintype.card_piFinset_const]

theorem success_card_add_failure_card {Ω : Type*} [Fintype Ω]
    (success : Ω → Prop) [DecidablePred success] (k : ℕ) :
    (Finset.univ.filter (fun s : Fin k → Ω => ∃ i, success (s i))).card +
        (Finset.univ.filter (fun ω => ¬ success ω)).card ^ k =
      Fintype.card Ω ^ k := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → Ω)))
    (p := fun s => ∃ i, success (s i))
  simp only [not_exists] at h
  rw [all_failure_card (fun ω => ¬ success ω) k] at h
  simpa only [Finset.card_univ, Fintype.card_pi_const] using h

theorem success_fraction {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (success : Ω → Prop) [DecidablePred success] (k : ℕ) :
    ((Finset.univ.filter (fun s : Fin k → Ω => ∃ i, success (s i))).card : ℝ) /
        (Fintype.card (Fin k → Ω) : ℝ) =
      1 - (((Finset.univ.filter (fun ω => ¬ success ω)).card : ℝ) /
        (Fintype.card Ω : ℝ)) ^ k := by
  have hcard := success_card_add_failure_card success k
  have hreal :
      ((Finset.univ.filter (fun s : Fin k → Ω => ∃ i, success (s i))).card : ℝ) +
          ((Finset.univ.filter (fun ω => ¬ success ω)).card : ℝ) ^ k =
        (Fintype.card Ω : ℝ) ^ k := by exact_mod_cast hcard
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [Fintype.card_pi_const, Nat.cast_pow, div_pow]
  field_simp
  nlinarith

theorem expected_output_of_success_fraction {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (S : Finset Ω) (hS : ∀ ω ∈ S, t ≤ X ω) :
    t * ((S.card : ℝ) / (Fintype.card Ω : ℝ)) ≤
      (∑ ω, X ω) / (Fintype.card Ω : ℝ) := by
  classical
  have hsum : (S.card : ℝ) * t ≤ ∑ ω, X ω := by
    calc
      _ = ∑ _ω ∈ S, t := by simp
      _ ≤ ∑ ω ∈ S, X ω := Finset.sum_le_sum hS
      _ ≤ ∑ ω, X ω := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ S) (fun ω _ _ => hX ω)
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by simpa [mul_comm] using hsum) hpos.le

theorem repeated_expected_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) (k : ℕ)
    (Y : (Fin k → Ω) → ℝ)
    (hY : ∀ s, 0 ≤ Y s)
    (hmax : ∀ s i, X (s i) ≤ Y s) :
    t * (1 - (((Finset.univ.filter (fun ω => ¬ t ≤ X ω)).card : ℝ) /
      (Fintype.card Ω : ℝ)) ^ k) ≤
      (∑ s, Y s) / (Fintype.card (Fin k → Ω) : ℝ) := by
  classical
  rw [← success_fraction (fun ω => t ≤ X ω) k]
  apply expected_output_of_success_fraction Y t hY
  intro s hs
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hs).2
  exact hi.trans (hmax s i)

end QuantumMaxCutEnergy.Sampling

theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) (k : ℕ)
    (Y : (Fin k → Ω) → ℝ)
    (hY : ∀ s, 0 ≤ Y s)
    (hmax : ∀ s i, X (s i) ≤ Y s) :
    t * (1 - (((Finset.univ.filter (fun ω => ¬ t ≤ X ω)).card : ℝ) /
      (Fintype.card Ω : ℝ)) ^ k) ≤
      (∑ s, Y s) / (Fintype.card (Fin k → Ω) : ℝ) :=
  QuantumMaxCutEnergy.Sampling.repeated_expected_lower X t k Y hY hmax

#print axioms solution
