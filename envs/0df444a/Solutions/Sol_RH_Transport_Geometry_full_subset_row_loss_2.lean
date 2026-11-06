-- Prove2me | solution 2 for RH.Transport.Geometry.full_subset_row_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:20.811053+00:00
-- url     : https://prove2.me/submissions/3e28a91e-1874-4fae-afbb-262cf85e5374

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : 0 < p) :
    max 0 (5 * ell p - 1 + ell p) / 4 = 3 * p / 2 := by
  have hn : 0 ≤ 5 * ell p - 1 + ell p := by
    dsimp [ell]
    linarith
  rw [max_eq_right hn]
  dsimp [ell]
  ring
end RH.Transport.Geometry
