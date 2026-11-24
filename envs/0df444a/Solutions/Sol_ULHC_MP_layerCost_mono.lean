-- Prove2me | solution 1 for ULHC.MP.layerCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:47.151461+00:00
-- url     : https://prove2.me/submissions/880ad195-05fc-4540-a650-279b6b66c24a

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_P2M_ULHC_MP_lsum_mono__0cdf42948454
import Theorems.Thm_ULHC_MP_stepCost_mono

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  {ec ec' : α → α → ℕ} {sc sc' : α → ℕ} (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x)
include hE
namespace ULHC.MP
theorem _root_.solution : ∀ k, layerCost NL mid tgt edge w ec k ≤ layerCost NL mid tgt edge w ec' k
  | 0 => le_rfl
  | k + 1 => by
    simp only [layerCost, nextCost]
    have := solution k
    have := lsum_mono' NL (fun x => stepCost NL mid tgt ec (layer NL mid tgt edge w k) x + 1)
      (fun x => stepCost NL mid tgt ec' (layer NL mid tgt edge w k) x + 1)
      (fun x => by have := stepCost_mono NL mid tgt hE (layer NL mid tgt edge w k) x; omega)
    omega
end ULHC.MP
