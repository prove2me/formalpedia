-- Prove2me | solution 1 for RossSolandGAP.Bound.lagrangean_bound_valid_for_P
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:04:27.957287+00:00
-- url     : https://prove2.me/submissions/8a43b274-3b17-4a11-bb0a-da96e6704b7d

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model

open Finset


open RossSolandGAP.Bound

theorem solution {m n : ℕ} (c r : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (lam : Fin n → ℝ) :
    (∀ x, FeasibleP r b x → FeasibleLag r b x ∧ lagObj c lam x = cost c x) ∧
    ∀ L : ℝ, (∀ x, FeasibleLag r b x → L ≤ lagObj c lam x) →
      ∀ x, FeasibleP r b x → L ≤ cost c x := by
  have key : ∀ x, FeasibleP r b x → FeasibleLag r b x ∧ lagObj c lam x = cost c x := by
    intro x hx
    have hsum : ∑ j, lam j * (1 - ∑ i, x i j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hx.2.2 j]
      ring
    exact ⟨⟨hx.1, hx.2.1⟩, by rw [lagObj, hsum, add_zero]⟩
  refine ⟨key, ?_⟩
  intro L hL x hx
  have h1 : L ≤ lagObj c lam x := hL x (key x hx).1
  rwa [(key x hx).2] at h1

