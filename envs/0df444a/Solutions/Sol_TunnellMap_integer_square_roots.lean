-- Prove2me | solution 1 for TunnellMap.integer_square_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:00.488951+00:00
-- url     : https://prove2.me/submissions/50a2cd5e-eecf-49d1-b6d1-86d7a058be3a

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {u s : ℤ} (h : u ^ 2 = s ^ 2) :
    u = s ∨ u = -s := by
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h
end TunnellMap
