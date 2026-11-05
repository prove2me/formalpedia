-- Prove2me | solution 1 for SupplierAudit.Joint.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:40:44.026489+00:00
-- url     : https://prove2.me/submissions/056b0f12-fdc0-4761-ae9e-09105f44d4fc

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model
import Theorems.Thm_SupplierAudit_Joint_prop3_stability
import Theorems.Thm_SupplierAudit_Joint_prop3_thresholds

open SupplierAudit.Joint

theorem solution (P : SupplierAudit.Competition.Params) (hβ : 0 < P.β) (hscen : Scenario P) (hint : SupplierAudit.Competition.eHatI P < 1) :
    (∀ K : ℝ, 0 ≤ K → ∀ s₁ s₂ : Strategy, IsEquilibrium P K s₁ s₂ →
      ∀ x ∈ Feasible, IsMaxOn (aggProfit P K) Feasible x →
        unilProfit₁ P K s₁ s₂ + unilProfit₂ P K s₁ s₂ ≤ aggProfit P K x ∧
        (s₁ = s₂ →
          unilProfit₁ P K s₁ s₂ ≤ jointG₁ P x - Gamma₁ P K x ∧
          unilProfit₂ P K s₁ s₂ ≤ jointG₂ P x - Gamma₂ P K x)) ∧
    ∃ KL KH : ℝ, KL ≤ KH ∧ ∀ K : ℝ, 0 ≤ K →
      (K < KL → ∃ x ∈ Feasible, IsMaxOn (aggProfit P K) Feasible x ∧
          0 < x.1 ∧ 0 < x.2.1 ∧ x.2.2 = 0 ∧ 0 < deltaPi P x) ∧
      (KL ≤ K → K < KH → ∃ x ∈ Feasible, IsMaxOn (aggProfit P K) Feasible x ∧
          x.1 = 0 ∧ 0 < x.2.1 ∧ x.2.2 = 0 ∧ deltaPi P x = 0) ∧
      (KH ≤ K → IsMaxOn (aggProfit P K) Feasible (0, 0, 0)) := by
  refine ⟨fun K hK s₁ s₂ heq x hx hmax =>
      prop3_stability P hβ hscen hint K hK s₁ s₂ heq x hx hmax,
    KcL P, KcH P, ?_, fun K hK => prop3_thresholds P hβ hscen K hK⟩
  exact le_trans (min_le_left _ _) (le_max_left _ _)
