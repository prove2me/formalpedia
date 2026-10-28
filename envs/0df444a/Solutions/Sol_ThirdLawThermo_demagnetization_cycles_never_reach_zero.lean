-- Prove2me | solution 1 for ThirdLawThermo.demagnetization_cycles_never_reach_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:12:21.307695+00:00
-- url     : https://prove2.me/submissions/da87920b-8e96-4450-930a-39b98111de46

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology
open ThirdLawThermo

theorem solution {X : Type*} (S : ℝ → X → ℝ) (x₁ x₂ : X)
    (hmono₂ : StrictMonoOn (fun T => S T x₂) (Set.Ici 0))
    (hNernst : S 0 x₁ = S 0 x₂)
    (T : ℕ → ℝ) (m : ℕ) (hT₀ : 0 < T 0)
    (hstep : ∀ n < m, 0 ≤ T (n + 1) ∧ S (T (n + 1)) x₁ = S (T n) x₂) :
    0 < T m := by
  induction m with
  | zero => exact hT₀
  | succ k ih =>
    have ih' := ih (fun n hn => hstep n (by omega))
    obtain ⟨h0, hS⟩ := hstep k (by omega)
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := hmono₂ (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ih'.le) ih'
      simp only at h2
      rw [← hS, ← h, hNernst] at h2
      exact lt_irrefl _ h2
