-- Prove2me | solution 1 for PlotkinShmoysTardos.halving
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:19:20.844984+00:00
-- url     : https://prove2.me/submissions/4251e7f9-48f9-4915-a843-9ecda5b80b58

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality
import Definitions.Def_PlotkinShmoysTardos_improveGeneral

namespace Aux_PSTh

open PlotkinShmoysTardos

theorem step {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (L : ℝ) (s : CallState n)
    (h : s.tag = Tag.halved → lam A b d s.x < L / 2) :
    (callStep A b d ρ O L s).tag = Tag.halved → lam A b d (callStep A b d ρ O L s).x < L / 2 := by
  unfold callStep
  cases ht : s.tag with
  | running =>
    dsimp only
    split_ifs with h1 h2
    · intro _
      exact h1
    · intro h'
      exact absurd h' (by decide)
    · intro h'
      exact absurd h' (by decide)
  | halved =>
    dsimp only
    exact h
  | g2 =>
    dsimp only
    exact h

end Aux_PSTh

open PlotkinShmoysTardos Aux_PSTh in
theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (k : ℕ)
    (hk : (callRun A b d ρ O x k).tag = Tag.halved) :
    lam A b d (callRun A b d ρ O x k).x < lam A b d x / 2 := by
  have inv : ∀ k, (callRun A b d ρ O x k).tag = Tag.halved →
      lam A b d (callRun A b d ρ O x k).x < lam A b d x / 2 := by
    intro k
    induction k with
    | zero =>
      intro h
      simp [callRun] at h
    | succ k ih =>
      unfold callRun
      rw [Function.iterate_succ_apply']
      exact step A b d ρ O (lam A b d x) _ ih
  exact inv k hk
