-- Prove2me | solution 1 for Sendov.wsum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:22.976465+00:00
-- url     : https://prove2.me/submissions/318840e7-d72b-4e38-bf2e-dc2f5682d1fd

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_abs_le_l1
import Theorems.Thm_Sendov_l1row_qrow
import Theorems.Thm_Sendov_l1_wsum_le

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (g₀ g₁ g₂ : List ℤ) (k : ℕ) (L β : ℤ) (hL : 0 ≤ L)
    (hβ : 2 * (L * (l1 g₀ + l1 g₁ + l1 g₂) ^ k) < β) :
    ∀ a ∈ wsum L 0 (qrow g₀ g₁ g₂ k), 2 * |a| < β := by
  intro a ha
  have h1 : |a| ≤ l1 (wsum L 0 (qrow g₀ g₁ g₂ k)) := abs_le_l1 _ a ha
  have h2 := l1_wsum_le L hL (qrow g₀ g₁ g₂ k) 0
  have h3 : L * l1row (qrow g₀ g₁ g₂ k) ≤ L * (l1 g₀ + l1 g₁ + l1 g₂) ^ k :=
    mul_le_mul_of_nonneg_left (l1row_qrow g₀ g₁ g₂ k) hL
  omega
end Sendov
