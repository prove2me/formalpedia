-- Prove2me | solution 1 for RiskSensMDP.AverageCost.theorem_5_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:09:34.380917+00:00
-- url     : https://prove2.me/submissions/e7053713-72c8-4a88-b048-64e04dee0889
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_RiskSensMDP_AverageCost_Criterion
import Theorems.Thm_RiskSensMDP_AverageCost_theorem_5_1
import Theorems.Thm_RiskSensMDP_AverageCost_jensen_step

open MeasureTheory ProbabilityTheory Filter Finset

open RiskSensMDP.AverageCost in
theorem solution {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (γ : ℝ) (hγ : 1 ≤ γ) (hM : MDPPositiveHarris M)
    (fstar : StationaryRule M) (hopt : IsRiskNeutralOptimal M fstar) :
    (∀ (σ : Policy M) (x : E), powerAvgCost M γ fstar.toPolicy x ≤ powerAvgCost M γ σ x) ∧
    (∀ x : E, powerAvgCost M γ fstar.toPolicy x = optPowerAvgCost M γ x) := by
  obtain ⟨ρ, hργ, hρ1⟩ := theorem_5_1 M fstar (hM fstar)
  have hγ0 : 0 < γ := lt_of_lt_of_le one_pos hγ
  -- Theorem 5.1: `J_{π*}(x) = ρ = ρ_{π*}(x)`
  have hJ : ∀ x, powerAvgCost M γ fstar.toPolicy x = ρ := fun x => (hργ γ hγ0 x).limsup_eq
  have hR : ∀ x, riskNeutralAvgCost M fstar.toPolicy x = ρ := fun x => (hρ1 x).limsup_eq
  have part1 : ∀ (σ : Policy M) (x : E),
      powerAvgCost M γ fstar.toPolicy x ≤ powerAvgCost M γ σ x := by
    intro σ x
    calc powerAvgCost M γ fstar.toPolicy x = riskNeutralAvgCost M fstar.toPolicy x := by
          rw [hJ, hR]
      _ ≤ riskNeutralAvgCost M σ x := hopt σ x
      _ ≤ powerAvgCost M γ σ x := jensen_step M γ hγ σ x
  refine ⟨part1, fun x => ?_⟩
  unfold optPowerAvgCost
  apply le_antisymm
  · have : Nonempty (Policy M) := ⟨fstar.toPolicy⟩
    exact le_ciInf (fun σ => part1 σ x)
  · exact ciInf_le ⟨powerAvgCost M γ fstar.toPolicy x, by
      rintro _ ⟨σ, rfl⟩; exact part1 σ x⟩ fstar.toPolicy
