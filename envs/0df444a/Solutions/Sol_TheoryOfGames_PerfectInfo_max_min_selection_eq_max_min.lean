-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.max_min_selection_eq_max_min
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:24:13.461186+00:00
-- url     : https://prove2.me/submissions/8bb17a6c-306d-40f7-8fd9-5b1c67d60daa

import Mathlib

set_option autoImplicit false

/-- (13:G): for `ψ(x, u)` on finite nonempty domains, with `f` ranging over all functions from
the `x`-domain to the `u`-domain, `Max_x Min_f ψ(x, f(x)) = Max_x Min_u ψ(x, u)`. -/
theorem solution {X U : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype U] [Nonempty U] (ψ : X → U → ℝ) :
    (Finset.univ.sup' Finset.univ_nonempty fun x : X =>
        Finset.univ.inf' Finset.univ_nonempty fun f : X → U => ψ x (f x)) =
      Finset.univ.sup' Finset.univ_nonempty fun x : X =>
        Finset.univ.inf' Finset.univ_nonempty fun u : U => ψ x u := by
  congr 1
  funext x
  apply le_antisymm
  · apply Finset.le_inf'
    intro u _
    exact Finset.inf'_le _ (Finset.mem_univ (fun _ : X => u))
  · apply Finset.le_inf'
    intro f _
    exact Finset.inf'_le _ (Finset.mem_univ (f x))

