-- Prove2me | solution 1 for TarchaBraids.thm_3_11_half_twists_generate
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:10:48.270427+00:00
-- url     : https://prove2.me/submissions/2e0e866b-0ea1-4b5d-a000-25c6de035955

import Theorems.Thm_TarchaBraids_exists_surjective_halfTwist_hom
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false
open BraidsLinksMCG TarchaBraids

theorem _root_.solution (n : ℕ) :
    Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i)) =
      (⊤ : Subgroup (GeomBraidGroup n)) := by
  obtain ⟨f, hf, hsurj⟩ := TarchaBraids.exists_surjective_halfTwist_hom n
  have himg : Set.range (fun i : Fin (n - 1) => halfTwistBraid n i)
      = f '' (Set.range (fun i : Fin (n - 1) => sigma (n := n) i)) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => (hf i).symm)
  rw [himg, ← MonoidHom.map_closure]
  rw [show Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma (n := n) i))
        = (⊤ : Subgroup (ArtinBraidGroup n)) from PresentedGroup.closure_range_of _]
  rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr hsurj

#print axioms solution
