-- Prove2me | solution 1 for TarchaBraids.prop_3_13_two_braid_is_power
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T05:13:32.681975+00:00
-- url     : https://prove2.me/submissions/5cf61124-9ef0-4548-9ddd-de7413b4c6eb

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

open BraidsLinksMCG

theorem solution (b : ArtinBraidGroup 2) :
    ∃ m : ℤ, b = sigma (0 : Fin (2 - 1)) ^ m := by
  have hrange : (Set.range fun i : Fin (2 - 1) => sigma (n := 2) i)
      = ({sigma (0 : Fin (2 - 1))} : Set (ArtinBraidGroup 2)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have : i = 0 := by
        have hi := i.isLt
        ext
        omega
      simp [this]
    · rintro rfl
      exact ⟨0, rfl⟩
  have htop : Subgroup.closure ({sigma (0 : Fin (2 - 1))} : Set (ArtinBraidGroup 2)) = ⊤ := by
    rw [← hrange]
    exact PresentedGroup.closure_range_of (braidRels 2)
  have hb : b ∈ Subgroup.closure ({sigma (0 : Fin (2 - 1))} : Set (ArtinBraidGroup 2)) := by
    rw [htop]; trivial
  obtain ⟨m, hm⟩ := Subgroup.mem_closure_singleton.mp hb
  exact ⟨m, hm.symm⟩
