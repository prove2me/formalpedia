-- Prove2me | solution 1 for RetailerMarketplace.Entry.proposition_1_sbm
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:33:50.998702+00:00
-- url     : https://prove2.me/submissions/9188996e-dfe0-448a-bc1a-9ae408239df4

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model
import Definitions.Def_RetailerMarketplace_Entry_PricingGame

set_option autoImplicit false
open RetailerMarketplace.Entry

theorem solution (c lam v : ℝ) (hc : 0 < c) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hv : c ≤ v) :
    IsOptSBM c lam v v Steer.M ∧ uM_SBM c lam v v Steer.M = piSBM c v := by
  obtain ⟨hl0, hl1⟩ := hlam
  have hself : uM_SBM c lam v v Steer.M = v - c := by
    unfold uM_SBM qM_SBM
    simp
  refine ⟨?_, by rw [hself]; rfl⟩
  intro p S'
  rw [hself]
  unfold uM_SBM qM_SBM
  by_cases hp : p ≤ v
  · have hq0 : 0 ≤ (if S' = Steer.M ∧ p ≤ v then lam else 0) + (if p ≤ v then 1 - lam else 0) := by
      split_ifs <;> linarith
    have hq1 : (if S' = Steer.M ∧ p ≤ v then lam else 0) + (if p ≤ v then 1 - lam else 0) ≤ 1 := by
      split_ifs <;> linarith
    by_cases hpc : c ≤ p
    · nlinarith
    · push_neg at hpc
      nlinarith
  · simp [hp]
    linarith
