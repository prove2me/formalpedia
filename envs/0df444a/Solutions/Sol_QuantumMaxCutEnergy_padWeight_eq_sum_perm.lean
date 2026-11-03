-- Prove2me | solution 1 for QuantumMaxCutEnergy.padWeight_eq_sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T02:20:22.94681+00:00
-- url     : https://prove2.me/submissions/c716f8c3-8296-4eb4-bc77-c6cbb736470c

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Theorems.Thm_QuantumMaxCutEnergy_padWeight_mem_doublyStochastic
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

theorem solution {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, loadAt x v ≤ 1) :
    ∃ lam : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ lam σ) ∧ (∑ σ, lam σ = 1) ∧
      ∑ σ, lam σ • Equiv.Perm.permMatrix ℝ σ = padWeight x :=
  exists_eq_sum_perm_of_mem_doublyStochastic (padWeight_mem_doublyStochastic x hx hload)

#print axioms solution
