-- Prove2me | solution 1 for WilliamsonShmoys.finite_set_has_maximal_element
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:34.388308+00:00
-- url     : https://prove2.me/submissions/b9c0c794-bf03-45a0-91f8-8f9ada229553

import Mathlib
theorem solution
    {alpha : Type} [Finite alpha] [PartialOrder alpha]
    (s : Set alpha) (hne : s.Nonempty) :
    Exists fun a : alpha => And (a ∈ s)
      (forall b : alpha, a <= b -> b ∈ s -> b = a) := by
  obtain ⟨a, ha⟩ := (Set.toFinite s).exists_maximal hne
  exact ⟨a, ha.prop, fun b hab hb => le_antisymm (ha.2 hb hab) hab⟩
