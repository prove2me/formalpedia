-- Prove2me | solution 1 for RSF.primitive_comparison
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:42:36.42575+00:00
-- url     : https://prove2.me/submissions/bcf7ce7e-8c8c-4dcb-a23d-3e52fb55ff96

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

open RSF


/-- Comparison world with `A i = Unit` and `B i = Bool`, which are not equivalent. -/
def rsf86_cw : ComparisonWorld where
  P := 2
  hP := Nat.prime_two
  X := Unit
  properSmooth := True
  A := fun _ => Unit
  aadd := fun _ _ _ => ()
  azero := fun _ => ()
  B := fun _ => Bool
  badd := fun _ x _ => x
  bzero := fun _ => false

theorem solution : ¬ (∀ w : ComparisonWorld,
    w.properSmooth →
    ∃ e : ∀ i : ℤ, w.A i ≃ w.B i,
      (∀ (i : ℤ) (x y : w.A i),
        e i (w.aadd i x y) = w.badd i (e i x) (e i y)) ∧
      (∀ i : ℤ, e i (w.azero i) = w.bzero i)) := by
  intro h
  obtain ⟨e, -, -⟩ := h rsf86_cw trivial
  have : (e 0).symm true = (e 0).symm false := Subsingleton.elim (α := Unit) _ _
  exact Bool.noConfusion ((e 0).symm.injective this)
