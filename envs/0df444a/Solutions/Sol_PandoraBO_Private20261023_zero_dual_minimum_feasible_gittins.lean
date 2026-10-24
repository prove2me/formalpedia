-- Prove2me | solution 1 for PandoraBO.Private20261023.zero_dual_minimum_feasible_gittins
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:48:44.225826+00:00
-- url     : https://prove2.me/submissions/54dd94db-8128-4680-9cab-5e3a0ec09f27

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_zero_multiplier_gittins_limit
import Theorems.Thm_PandoraBO_Private20261023_weitzman_optimality
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Tracked reduction to the zero-index limit and positive-cost Weitzman milestones.
The limit's optimality is proved by passing the positive-cost optimality
inequality to the limit. Thus its existence is not hidden in an assumption,
and no unproved boundedness assertion is used to manipulate the real supremum.
-/

set_option autoImplicit false

open PandoraBO Filter

namespace PandoraBO.Private20261023.Reduction

/-- An attained global maximum equals the real supremum in `optimalValue`. -/
private theorem optimalValue_eq_of_optimal {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (π : Policy n) (hopt : optimal M multiplier π) :
    optimalValue M multiplier = value M multiplier π := by
  unfold optimalValue
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨value M multiplier π, π, rfl⟩
    · rintro r ⟨ρ, rfl⟩
      exact hopt ρ
  · apply le_csSup
    · refine ⟨value M multiplier π, ?_⟩
      rintro r ⟨ρ, rfl⟩
      exact hopt ρ
    · exact ⟨π, rfl⟩

end PandoraBO.Private20261023.Reduction

theorem solution {n : ℕ} (M : Instance n)
    (B : ℝ) (hmin : dualMinimizer M B 0) :
    ∃ π : Policy n, isZeroGittinsPolicy M π ∧
      budgetFeasible M B π ∧ expectedReward M π = fullInformationReward M ∧
      optimal M 0 π := by
  let multipliers : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hpos : ∀ k, 0 < multipliers k := by
    intro k
    dsimp [multipliers]
    positivity
  have hmono : Antitone multipliers := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    have hcast : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    linarith
  have hlim : Tendsto multipliers atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨policies, π, hindices, hzeroindex, hfull, hcostlim, hrewardlim⟩ :=
    PandoraBO.Private20261023.zero_multiplier_gittins_limit
      M multipliers hpos hmono hlim
  have hoptseq : ∀ k, optimal M (multipliers k) (policies k) := by
    intro k
    exact (PandoraBO.Private20261023.weitzman_optimality
      M (multipliers k) (hpos k)).2 (policies k) (hindices k)
  have hoptzero : optimal M 0 π := by
    intro ρ
    have hleft : Tendsto
        (fun k => expectedReward M ρ - multipliers k * expectedCost M ρ)
        atTop (nhds (expectedReward M ρ - 0 * expectedCost M ρ)) :=
      tendsto_const_nhds.sub (hlim.mul tendsto_const_nhds)
    have hright : Tendsto
        (fun k => expectedReward M (policies k) -
          multipliers k * expectedCost M (policies k))
        atTop (nhds (expectedReward M π - 0 * expectedCost M π)) :=
      hrewardlim.sub (hlim.mul hcostlim)
    exact le_of_tendsto_of_tendsto' hleft hright (fun k => hoptseq k ρ)
  have hcostbound : ∀ k, expectedCost M (policies k) ≤ B := by
    intro k
    have hdual := hmin.2 (multipliers k) (hpos k).le
    change optimalValue M 0 + 0 * B ≤
      optimalValue M (multipliers k) + multipliers k * B at hdual
    rw [PandoraBO.Private20261023.Reduction.optimalValue_eq_of_optimal
      M 0 π hoptzero,
      PandoraBO.Private20261023.Reduction.optimalValue_eq_of_optimal
        M (multipliers k) (policies k) (hoptseq k)] at hdual
    have hreward := hoptzero (policies k)
    simp only [value, zero_mul, sub_zero, zero_add, add_zero] at hdual hreward
    have hscaled : multipliers k * expectedCost M (policies k) ≤
        multipliers k * B := by linarith
    exact (mul_le_mul_iff_right₀ (hpos k)).mp hscaled
  have hfeasible : budgetFeasible M B π :=
    le_of_tendsto_of_tendsto' hcostlim tendsto_const_nhds hcostbound
  exact ⟨π, hzeroindex, hfeasible, hfull, hoptzero⟩
