-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_braidInterp_reflection_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:17:07.44592+00:00
-- url     : https://prove2.me/submissions/fe22188a-8b40-4347-be44-54e6849c86ed

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ (u : ℝ) (c z w : ℂ),
      braidInterp u (c - z) (c - w) = c - braidInterp u z w := by
  intro u c z w
  apply Complex.ext <;> simp [braidInterp] <;> ring
