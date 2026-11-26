-- Prove2me | solution 1 for Sendov.qrow_entry_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:17:25.562863+00:00
-- url     : https://prove2.me/submissions/9c820246-3d0c-499f-9291-07b76a922e45

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
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsumZ_cons
import Theorems.Thm_Sendov_mem_radd_length_le
import Theorems.Thm_Sendov_mem_rscale_length_le
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
theorem _root_.solution (g₀ g₁ g₂ : List ℤ) (G : ℕ)
    (h0 : g₀.length ≤ G) (h1 : g₁.length ≤ G) (h2 : g₂.length ≤ G) :
    ∀ (k : ℕ), ∀ p ∈ qrow g₀ g₁ g₂ k, p.length ≤ 1 + G * k := by
  intro k
  induction k with
  | zero =>
    intro p hp
    simp only [qrow, List.mem_singleton] at hp
    subst hp
    simp
  | succ k ih =>
    intro p hp
    have hGk : G * (k + 1) = G * k + G := by ring
    have hb : ∀ q ∈ qrow g₀ g₁ g₂ k, q.length ≤ 1 + G * k := ih
    have e0 : ∀ x ∈ rscale g₀ (qrow g₀ g₁ g₂ k), x.length ≤ 1 + G * (k + 1) := by
      intro x hx; have := mem_rscale_length_le g₀ _ hb x hx; omega
    have e1 : ∀ x ∈ ([] : List ℤ) :: rscale g₁ (qrow g₀ g₁ g₂ k),
        x.length ≤ 1 + G * (k + 1) := by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · subst h; simp
      · have := mem_rscale_length_le g₁ _ hb x h; omega
    have e2 : ∀ x ∈ ([] : List ℤ) :: ([] : List ℤ) :: rscale g₂ (qrow g₀ g₁ g₂ k),
        x.length ≤ 1 + G * (k + 1) := by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · subst h; simp
      rcases List.mem_cons.1 h with h' | h'
      · subst h'; simp
      · have := mem_rscale_length_le g₂ _ hb x h'; omega
    exact mem_radd_length_le _ _ e0 (mem_radd_length_le _ _ e1 e2) p hp
end Sendov
