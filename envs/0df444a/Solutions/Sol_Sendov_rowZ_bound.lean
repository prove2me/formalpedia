-- Prove2me | solution 1 for Sendov.rowZ_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:18:24.067593+00:00
-- url     : https://prove2.me/submissions/5d9177c6-11cd-45f6-a8dd-6de08bf6e1a9

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_wsum_nil
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_l1_nil
import Theorems.Thm_Sendov_l1_cons
import Theorems.Thm_Sendov_l1_nonneg
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_l1row_qrow
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_abs_pevZ_le
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsumZ_cons
import Theorems.Thm_Sendov_qrow_entry_length_le
import Theorems.Thm_Sendov_l1_le_l1row
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


attribute [local simp] Sendov.rowZ_nil
attribute [local simp] Sendov.rowZ_cons
attribute [local simp] Sendov.rowZ_length
attribute [local simp] Sendov.wsum_nil
attribute [local simp] Sendov.wsum_cons
attribute [local simp] Sendov.l1_nil
attribute [local simp] Sendov.l1_cons
attribute [local simp] Sendov.l1row_nil
attribute [local simp] Sendov.l1row_cons
attribute [local simp] Sendov.rscale_length
attribute [local simp] Sendov.qrow_length
attribute [local simp] Sendov.wsumZ_nil
attribute [local simp] Sendov.wsumZ_cons

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (g₀ g₁ g₂ : List ℤ) (k G : ℕ) (β τ : ℤ) (hβ : 1 ≤ β)
    (h0 : g₀.length ≤ G) (h1 : g₁.length ≤ G) (h2 : g₂.length ≤ G)
    (hτ : 2 * ((l1 g₀ + l1 g₁ + l1 g₂) ^ k * β ^ (1 + G * k)) < τ) :
    ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ := by
  intro a ha
  simp only [rowZ, List.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  have hlen : p.length ≤ 1 + G * k := qrow_entry_length_le g₀ g₁ g₂ G h0 h1 h2 k p hp
  have hl1p : l1 p ≤ (l1 g₀ + l1 g₁ + l1 g₂) ^ k :=
    le_trans (l1_le_l1row _ p hp) (l1row_qrow g₀ g₁ g₂ k)
  have hpow : β ^ p.length ≤ β ^ (1 + G * k) := pow_le_pow_right₀ hβ hlen
  have hbpos : (0 : ℤ) < β ^ p.length := by positivity
  have habs := abs_pevZ_le β hβ p
  have hl1nn := l1_nonneg p
  have : |pevZ p β| ≤ (l1 g₀ + l1 g₁ + l1 g₂) ^ k * β ^ (1 + G * k) := by
    calc |pevZ p β| ≤ l1 p * β ^ p.length := habs
      _ ≤ (l1 g₀ + l1 g₁ + l1 g₂) ^ k * β ^ (1 + G * k) := by
          apply mul_le_mul hl1p hpow hbpos.le
          exact le_trans hl1nn hl1p
  omega
end Sendov
