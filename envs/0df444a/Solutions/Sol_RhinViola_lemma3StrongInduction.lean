-- Prove2me | solution 1 for RhinViola.lemma3StrongInduction
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T16:52:36.783486+00:00
-- url     : https://prove2.me/submissions/05fb3bbc-9995-45e2-b4e5-2598b2739703

import Mathlib.Tactic

theorem solution
    (P : ℕ → ℕ → ℕ → Prop)
    (hbase : ∀ k l nu : ℕ, nu ≤ k + l →
      (k = 0 ∨ l = 0 ∨ nu = 0 ∨ nu = k + l) → P k l nu)
    (hstep : ∀ k l nu : ℕ,
      0 < k → 0 < l → 0 < nu → nu < k + l →
      P (k - 1) (l - 1) (nu - 1) →
      P k (l - 1) nu →
      P (k - 1) l nu →
      P k l nu) :
    ∀ k l nu : ℕ, nu ≤ k + l → P k l nu := by
  have key : ∀ n, ∀ k l nu : ℕ, k + l + nu = n → nu ≤ k + l → P k l nu := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k l nu hn hle
      by_cases h : k = 0 ∨ l = 0 ∨ nu = 0 ∨ nu = k + l
      · exact hbase k l nu hle h
      · push_neg at h
        obtain ⟨hk, hl, hnu, hne⟩ := h
        apply hstep k l nu (by omega) (by omega) (by omega) (by omega)
        · exact ih _ (by omega) _ _ _ rfl (by omega)
        · exact ih _ (by omega) _ _ _ rfl (by omega)
        · exact ih _ (by omega) _ _ _ rfl (by omega)
  intro k l nu hle
  exact key _ k l nu rfl hle
