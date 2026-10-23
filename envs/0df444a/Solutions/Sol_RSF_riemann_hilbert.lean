-- Prove2me | solution 1 for RSF.riemann_hilbert
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:41:23.309873+00:00
-- url     : https://prove2.me/submissions/308f4cb8-48c1-4dcd-a98c-e6896d2a7878

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

open RSF


/-- Riemann–Hilbert world whose functor collapses two distinct morphisms. -/
def rsf86_rh : RHWorld where
  Sheaf := Unit
  PhiMod := Unit
  Hom1 := fun _ _ => Bool
  Hom2 := fun _ _ => Unit
  T := fun _ => ()
  Tmor := fun _ _ _ => ()
  IsPerfect := fun _ => True

theorem solution : ¬ (∀ w : RHWorld,
    (∀ A B : w.Sheaf, Function.Bijective (w.Tmor A B)) ∧
    (∀ M : w.PhiMod, w.IsPerfect M → ∃ N : w.Sheaf, w.T N = M) ∧
    (∀ N : w.Sheaf, w.IsPerfect (w.T N))) := by
  intro h
  have := ((h rsf86_rh).1 () ()).1 (a₁ := true) (a₂ := false) rfl
  exact Bool.noConfusion this
