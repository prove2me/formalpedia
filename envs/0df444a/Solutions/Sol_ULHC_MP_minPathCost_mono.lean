-- Prove2me | solution 1 for ULHC.MP.minPathCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:04.263863+00:00
-- url     : https://prove2.me/submissions/519897e1-aebe-4dab-95fe-340c55ac4bf1

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_ULHC_MP_minPathLCost_mono

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
namespace ULHC.MP
theorem _root_.solution {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) {ec ec' : β → β → ℕ} {sc sc' : β → ℕ}
    (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x) :
    minPathCost N mid tgt edge w ec sc ≤ minPathCost N mid tgt edge w ec' sc' := by
  have := minPathLCost_mono (N.sort (· ≤ ·)) mid tgt edge w hE hS
  unfold minPathCost
  omega
end ULHC.MP
