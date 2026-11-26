-- Prove2me | solution 1 for Sendov.rowZ_qrow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:07.270847+00:00
-- url     : https://prove2.me/submissions/37cdd38b-1c34-4bad-a28a-f4dc20842128

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_pevZ_rowZ_qrow
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackZ_pevZ
import Theorems.Thm_Sendov_unpackZ_succ
import Theorems.Thm_Sendov_unpackZ_zero
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackZ_succ
attribute [local simp] Sendov.unpackZ_zero


attribute [local simp] Sendov.rowZ_length

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (g₀ g₁ g₂ : List ℤ) (k : ℕ) (β τ : ℤ) (hτ : 0 < τ)
    (hbound : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ) :
    unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)
      = rowZ (qrow g₀ g₁ g₂ k) β := by
  rw [← pevZ_rowZ_qrow, ← rowZ_length (qrow g₀ g₁ g₂ k) β]
  exact unpackZ_pevZ τ hτ _ hbound
end Sendov
