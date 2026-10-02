-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.max_min_selection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:10:29.948644+00:00
-- url     : https://prove2.me/submissions/b1588582-2c22-47e7-842a-5f73649f0d01

import Mathlib

set_option autoImplicit false

theorem solution {X U : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype U] [Nonempty U] (ψ : X → U → ℝ) :
    (Finset.univ.sup' Finset.univ_nonempty fun x : X =>
        Finset.univ.inf' Finset.univ_nonempty fun f : X → U => ψ x (f x)) =
      Finset.univ.inf' Finset.univ_nonempty fun f : X → U =>
        Finset.univ.sup' Finset.univ_nonempty fun x : X => ψ x (f x) := by
  -- a minimizing selection
  have hmin : ∀ x : X, ∃ u : U, ∀ v : U, ψ x u ≤ ψ x v := by
    intro x
    obtain ⟨u, -, hu⟩ := Finset.exists_min_image Finset.univ (ψ x) Finset.univ_nonempty
    exact ⟨u, fun v => hu v (Finset.mem_univ v)⟩
  choose f0 hf0 using hmin
  apply le_antisymm
  · -- LHS ≤ RHS
    apply Finset.le_inf'
    intro f _
    apply Finset.sup'_le
    intro x _
    exact le_trans (Finset.inf'_le _ (Finset.mem_univ f))
      (Finset.le_sup' (fun x : X => ψ x (f x)) (Finset.mem_univ x))
  · -- RHS ≤ LHS via f0
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ f0)) ?_
    apply Finset.sup'_le
    intro x _
    refine le_trans ?_ (Finset.le_sup' (fun x : X =>
        Finset.univ.inf' Finset.univ_nonempty fun f : X → U => ψ x (f x)) (Finset.mem_univ x))
    apply Finset.le_inf'
    intro g _
    exact hf0 x (g x)
