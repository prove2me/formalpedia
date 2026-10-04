-- Prove2me | solution 1 for TarchaBraids.geom_null_word_mul_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:35:03.365877+00:00
-- url     : https://prove2.me/submissions/b840a00c-a425-4451-baa9-6dd9bb4afb49

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

open TarchaBraids in
theorem solution (n : ℕ) (w₁ w₂ : FreeGroup (Fin (n - 1)))
    (h₁ : FreeGroup.lift (halfTwistBraid n) w₁ = 1)
    (h₂ : FreeGroup.lift (halfTwistBraid n) w₂ = 1) :
    FreeGroup.lift (halfTwistBraid n) (w₁ * w₂) = 1 := by
  rw [map_mul, h₁, h₂, one_mul]

#print axioms solution
