-- Prove2me | solution 1 for Sendov.pevZ_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:11:09.943891+00:00
-- url     : https://prove2.me/submissions/3b851631-f23b-4bf9-af3a-28d343a73705

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_unpackZ_pevZ


set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (β : ℤ) (hβ : 0 < β) (p q : List ℤ)
    (hp : ∀ a ∈ p, 2 * |a| < β) (hq : ∀ a ∈ q, 2 * |a| < β)
    (hlen : p.length = q.length) (h : pevZ p β = pevZ q β) : p = q := by
  have h1 := unpackZ_pevZ β hβ p hp
  have h2 := unpackZ_pevZ β hβ q hq
  rw [← h1, ← h2, hlen, h]
end Sendov
