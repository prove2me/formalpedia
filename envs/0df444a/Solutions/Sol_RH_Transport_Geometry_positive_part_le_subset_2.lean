-- Prove2me | solution 2 for RH.Transport.Geometry.positive_part_le_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:23:45.47147+00:00
-- url     : https://prove2.me/submissions/e650571e-1b67-4865-8072-4cebc9e0f4b9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
import Theorems.Thm_RH_Transport_Geometry_ell_lt_one_fifth

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    max 0 (5 * ell p - 1 + d) ≤ d := by
  have he := ell_lt_one_fifth hp
  apply max_le
  · exact hd
  · linarith
end RH.Transport.Geometry
