-- Prove2me | solution 1 for SethiChengSS.Finite.proposition_4_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:56:15.851182+00:00
-- url     : https://prove2.me/submissions/8454d92b-deb5-4a28-b88f-92e2b3dffc00

import Mathlib
import Definitions.Def_BertsekasKConvex
set_option autoImplicit false

theorem solution (K L α β : ℝ) (g₁ g₂ : ℝ → ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (h₁ : BertsekasKConvex K g₁) (h₂ : BertsekasKConvex L g₂) :
    BertsekasKConvex (α * K + β * L) (fun x => α * g₁ x + β * g₂ x) := by
  intro z b y hz hb
  have e1 := mul_le_mul_of_nonneg_left (h₁ z b y hz hb) hα
  have e2 := mul_le_mul_of_nonneg_left (h₂ z b y hz hb) hβ
  show (α * g₁ y + β * g₂ y) + (z / b) * ((α * g₁ y + β * g₂ y) - (α * g₁ (y - b) + β * g₂ (y - b))) ≤ (α * K + β * L) + (α * g₁ (z + y) + β * g₂ (z + y))
  nlinarith [e1, e2]
