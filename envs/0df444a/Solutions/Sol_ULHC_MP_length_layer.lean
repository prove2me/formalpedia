-- Prove2me | solution 1 for ULHC.MP.length_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:06.195541+00:00
-- url     : https://prove2.me/submissions/9acde91d-1358-4725-9d0a-98e044dd1d88

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
namespace ULHC.MP
theorem _root_.solution (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ) :
    ∀ k, (layer NL mid tgt edge w k).length ≤ NL.length
  | 0 => by simp [layer]
  | k + 1 => by simp [layer, next]
end ULHC.MP
