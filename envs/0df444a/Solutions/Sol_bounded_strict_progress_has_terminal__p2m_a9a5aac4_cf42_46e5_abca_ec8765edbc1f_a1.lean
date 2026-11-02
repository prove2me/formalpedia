-- Prove2me | solution 1 for bounded_strict_progress_has_terminal__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:17.808093+00:00
-- url     : https://prove2.me/submissions/7b648f2c-6786-4b1b-8eb6-5e51472b5157

import Mathlib

theorem solution
    {α : Type} (P Q : α → Prop) (μ : α → Nat) (N : Nat)
    (hbase : ∃ a : α, P a)
    (hbound : ∀ a : α, P a → μ a ≤ N)
    (hprogress : ∀ a : α, P a → ¬ Q a → ∃ b : α, P b ∧ μ a < μ b) :
    ∃ a : α, P a ∧ Q a := by
  have haux : ∀ k : Nat, ∀ a : α, N - μ a = k → P a → ∃ b : α, P b ∧ Q b := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a hk ha
      by_cases hqa : Q a
      · exact ⟨a, ha, hqa⟩
      · obtain ⟨b, hb, hab⟩ := hprogress a ha hqa
        have hdecr : N - μ b < k := by
          have hbb := hbound b hb
          omega
        exact ih (N - μ b) hdecr b rfl hb
  obtain ⟨a, ha⟩ := hbase
  exact haux (N - μ a) a rfl ha