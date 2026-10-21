-- Prove2me | solution 1 for PerishablePricing.Backlog.constraint_set_lnat_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:41:25.42799+00:00
-- url     : https://prove2.me/submissions/132edc7c-0b49-4508-8347-b8b836491594

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

set_option autoImplicit false
open PerishablePricing.Backlog

theorem solution (L : ℕ) (hL : 1 ≤ L) (ε : ℝ) :
    LNatConvexSet {w : Fin (L + 3) → ℝ |
      w ⟨0, by omega⟩ ≤ w ⟨L + 2, by omega⟩ ∧
        w ⟨L + 1, by omega⟩ + ε ≤ w ⟨L + 2, by omega⟩} := by
  intro u hu v hv α hα
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    exact min_le_min (by linarith) hv1
  · simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    have h1 := min_le_left (u ⟨L + 1, by omega⟩ + α) (v ⟨L + 1, by omega⟩)
    have h2 := min_le_right (u ⟨L + 1, by omega⟩ + α) (v ⟨L + 1, by omega⟩)
    exact le_min (by linarith) (by linarith)
  · simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    exact max_le_max hu1 (by linarith)
  · simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    have h := max_le (a := u ⟨L + 1, by omega⟩) (b := v ⟨L + 1, by omega⟩ - α)
      (c := max (u ⟨L + 2, by omega⟩) (v ⟨L + 2, by omega⟩ - α) - ε)
      (by linarith [le_max_left (u ⟨L + 2, by omega⟩) (v ⟨L + 2, by omega⟩ - α)])
      (by linarith [le_max_right (u ⟨L + 2, by omega⟩) (v ⟨L + 2, by omega⟩ - α)])
    linarith
