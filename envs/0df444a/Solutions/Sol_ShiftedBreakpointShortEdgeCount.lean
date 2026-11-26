-- Prove2me | solution 1 for ShiftedBreakpointShortEdgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:24.814399+00:00
-- url     : https://prove2.me/submissions/150d0c80-a283-4376-ba59-39a579883797

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount

set_option autoImplicit false
open Set
theorem _root_.solution (k n p q c d : ℕ) (δ σ a' b' : ℝ) (s sA : ℕ → ℝ)
    (hp : 1 ≤ p) (hd : d + 1 ≤ p + c)
    (hcorr : ∀ i : ℕ, p - 1 ≤ i → i ≤ q → i + c - d ≤ k ∧ sA i = s (i + c - d) + σ)
    (hcount : ((Finset.Icc 1 k).filter
      (fun j => a' - σ ≤ s (j - 1) ∧ s j ≤ b' - σ ∧ s j - s (j - 1) < δ)).card ≤ n) :
    ((Finset.Icc p q).filter
      (fun i => a' ≤ sA (i - 1) ∧ sA i ≤ b' ∧ sA i - sA (i - 1) < δ)).card ≤ n := by
-- BODY
  refine le_trans (Finset.card_le_card_of_injOn (fun i => i + c - d) ?_ ?_) hcount
  · intro i hi
    obtain ⟨hiI, hlo, hhi, hshort⟩ := Finset.mem_filter.mp hi
    obtain ⟨hip, hiq⟩ := Finset.mem_Icc.mp hiI
    obtain ⟨hle, heq⟩ := hcorr i (by omega) hiq
    obtain ⟨-, heq'⟩ := hcorr (i - 1) (by omega) (by omega)
    have hidx : i + c - d - 1 = i - 1 + c - d := by omega
    have hA : s (i + c - d) = sA i - σ := by rw [heq]; ring
    have hB : s (i + c - d - 1) = sA (i - 1) - σ := by rw [hidx, heq']; ring
    show i + c - d ∈ Finset.filter
      (fun j => a' - σ ≤ s (j - 1) ∧ s j ≤ b' - σ ∧ s j - s (j - 1) < δ) (Finset.Icc 1 k)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_, ?_, ?_⟩
    · rw [hB]; linarith
    · rw [hA]; linarith
    · rw [hA, hB]; linarith
  · intro x hx y hy hxy
    obtain ⟨hxI, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    obtain ⟨hyI, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    obtain ⟨hxp, -⟩ := Finset.mem_Icc.mp hxI
    obtain ⟨hyp, -⟩ := Finset.mem_Icc.mp hyI
    have hxy' : x + c - d = y + c - d := hxy
    omega
