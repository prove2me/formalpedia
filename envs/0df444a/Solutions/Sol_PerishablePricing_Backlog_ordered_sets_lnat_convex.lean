-- Prove2me | solution 1 for PerishablePricing.Backlog.ordered_sets_lnat_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:38:54.735016+00:00
-- url     : https://prove2.me/submissions/45bbf14e-f4ec-453a-8d3d-eed4b6849e59

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

set_option autoImplicit false
open PerishablePricing.Backlog

theorem solution (n k : ℕ) (hk : k ≤ n) :
    LNatConvexSet (V n k) ∧ LNatConvexSet (Vplus n k) := by
  have hV : LNatConvexSet (V n k) := by
    intro u hu v hv α hα
    constructor
    · intro i j hij hjk
      simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
      exact min_le_min (by linarith [hu i j hij hjk]) (hv i j hij hjk)
    · intro i j hij hjk
      simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
      exact max_le_max (hu i j hij hjk) (by linarith [hv i j hij hjk])
  refine ⟨hV, ?_⟩
  intro u hu v hv α hα
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨h1, h2⟩ := hV u hu1 v hv1 α hα
  refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩
  · intro i hi
    simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    exact le_min (by linarith [hu2 i hi]) (hv2 i hi)
  · intro i hi
    simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    exact le_trans (hu2 i hi) (le_max_left _ _)
