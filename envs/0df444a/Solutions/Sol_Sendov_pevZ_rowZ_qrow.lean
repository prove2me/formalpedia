-- Prove2me | solution 1 for Sendov.pevZ_rowZ_qrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:26.866206+00:00
-- url     : https://prove2.me/submissions/26de1d19-b9e3-4e03-8eb8-90878467107b

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_pev_intCast
import Theorems.Thm_Sendov_rev_intCast
import Theorems.Thm_Sendov_rev_qrow


set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (g₀ g₁ g₂ : List ℤ) (k : ℕ) (β τ : ℤ) :
    pevZ (rowZ (qrow g₀ g₁ g₂ k) β) τ
      = (pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k := by
  have h := rev_qrow g₀ g₁ g₂ k (β : ℝ) (τ : ℝ)
  rw [rev_intCast, pev_intCast, pev_intCast, pev_intCast] at h
  exact_mod_cast h
end Sendov
