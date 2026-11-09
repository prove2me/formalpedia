-- Prove2me | solution 1 for TightQLearning.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:23:58.538347+00:00
-- url     : https://prove2.me/submissions/187e20b4-4859-4876-bec3-a7ffbc51d7dd

import Mathlib
import Definitions.Def_TightQLearning_syncQ

open QLearning.Convergence

open TightQLearning in
theorem solution {X A : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : FiniteMDP X A)
    (hr : ∀ s a, 0 ≤ M.R s a ∧ M.R s a ≤ 1) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1)
    (η : ℕ → ℝ) (Q0 : X → A → ℝ) (hQ0 : ∀ s a, 0 ≤ Q0 s a ∧ Q0 s a ≤ 1 / (1 - γ))
    (σ : ℕ → X → A → X) (T : ℕ) (hη : ∀ t, t ≤ T → 0 ≤ η t ∧ η t ≤ 1) :
    ∀ t, t ≤ T →
      (∀ s a, 0 ≤ syncQ M γ η Q0 σ t s a ∧ syncQ M γ η Q0 σ t s a ≤ 1 / (1 - γ)) ∧
      (∀ s, 0 ≤ vmax (syncQ M γ η Q0 σ t) s ∧ vmax (syncQ M γ η Q0 σ t) s ≤ 1 / (1 - γ)) := by
  have h1γ : 0 < 1 - γ := by linarith
  obtain ⟨B, hBd⟩ : ∃ B, B = 1 / (1 - γ) := ⟨_, rfl⟩
  rw [← hBd] at hQ0 ⊢
  have hB0 : 0 ≤ B := by rw [hBd]; exact div_nonneg zero_le_one h1γ.le
  have h1γn := h1γ.ne'
  have hB : 1 + γ * B = B := by
    rw [hBd]; field_simp <;> ring
  have hv : ∀ Q : X → A → ℝ, (∀ s a, 0 ≤ Q s a ∧ Q s a ≤ B) →
      ∀ s, 0 ≤ vmax Q s ∧ vmax Q s ≤ B := by
    intro Q hQ s
    unfold vmax
    obtain ⟨a0⟩ := ‹Nonempty A›
    exact ⟨(hQ s a0).1.trans (Finset.le_sup' (Q s) (Finset.mem_univ a0)),
      Finset.sup'_le _ _ fun a _ => (hQ s a).2⟩
  have main : ∀ t, t ≤ T → ∀ s a, 0 ≤ syncQ M γ η Q0 σ t s a ∧ syncQ M γ η Q0 σ t s a ≤ B := by
    intro t
    induction t with
    | zero => intro _; exact hQ0
    | succ t ih =>
      intro ht s a
      have ih' := ih (by omega)
      obtain ⟨v0, v1⟩ := hv _ ih' (σ (t + 1) s a)
      obtain ⟨e0, e1⟩ := hη (t + 1) ht
      obtain ⟨r0, r1⟩ := hr s a
      obtain ⟨q0, q1⟩ := ih' s a
      simp only [syncQ]
      have hw : M.R s a + γ * vmax (syncQ M γ η Q0 σ t) (σ (t + 1) s a) ≤ B := by
        nlinarith [mul_le_mul_of_nonneg_left v1 hγ.1.le]
      have hw0 : 0 ≤ M.R s a + γ * vmax (syncQ M γ η Q0 σ t) (σ (t + 1) s a) := by
        nlinarith [mul_nonneg hγ.1.le v0]
      have h1e : 0 ≤ 1 - η (t + 1) := by linarith
      constructor
      · nlinarith [mul_nonneg h1e q0, mul_nonneg e0 hw0]
      · nlinarith [mul_le_mul_of_nonneg_left q1 h1e, mul_le_mul_of_nonneg_left hw e0]
  exact fun t ht => ⟨main t ht, hv _ (main t ht)⟩
