-- Prove2me | solution 1 for ULHC.MP.minPathLCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:28.055401+00:00
-- url     : https://prove2.me/submissions/86eabaec-a4ce-4dc6-bf51-f04efd3640db

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_P2M_ULHC_MP_lsum_mono__0cdf42948454
import Theorems.Thm_ULHC_MP_layerCost_mono

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  {ec ec' : α → α → ℕ} {sc sc' : α → ℕ} (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x)
include hE hS
namespace ULHC.MP
theorem _root_.solution : minPathLCost NL mid tgt edge w ec sc ≤ minPathLCost NL mid tgt edge w ec' sc' := by
  have h1 := layerCost_mono NL mid tgt edge w hE NL.length
  have h2 := lsum_mono' NL (fun x => sc x + lookCost (layer NL mid tgt edge w NL.length) + 2)
    (fun x => sc' x + lookCost (layer NL mid tgt edge w NL.length) + 2) (fun x => by have := hS x; omega)
  unfold minPathLCost pickSrcCost
  omega
end ULHC.MP
