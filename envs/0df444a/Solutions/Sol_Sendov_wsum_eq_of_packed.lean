-- Prove2me | solution 1 for Sendov.wsum_eq_of_packed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:51.908543+00:00
-- url     : https://prove2.me/submissions/7267160c-71a2-495a-a5fa-9c1c9506a400

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_rowZ_qrow_eq
import Theorems.Thm_Sendov_pevZ_wsum
import Theorems.Thm_Sendov_pevZ_inj

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (g₀ g₁ g₂ : List ℤ) (k : ℕ) (L β τ : ℤ) (Nmom : List ℤ)
    (hβ : 0 < β) (hτ : 0 < τ)
    (hbτ : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ)
    (hbN : ∀ a ∈ Nmom, 2 * |a| < β)
    (hbW : ∀ a ∈ wsum L 0 (qrow g₀ g₁ g₂ k), 2 * |a| < β)
    (hlen : Nmom.length = (wsum L 0 (qrow g₀ g₁ g₂ k)).length)
    (hcheck : wsumZ L 0 (unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)) = pevZ Nmom β) :
    Nmom = wsum L 0 (qrow g₀ g₁ g₂ k) := by
  rw [rowZ_qrow_eq g₀ g₁ g₂ k β τ hτ hbτ, ← pevZ_wsum] at hcheck
  exact pevZ_inj β hβ _ _ hbN hbW hlen hcheck.symm
end Sendov
