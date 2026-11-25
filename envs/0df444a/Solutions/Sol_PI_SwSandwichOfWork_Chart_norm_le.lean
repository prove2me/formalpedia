-- Prove2me | solution 1 for PI.SwSandwichOfWork.Chart_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:16.027435+00:00
-- url     : https://prove2.me/submissions/7211243a-3f13-48dd-a4dd-e0a653c9c37e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option linter.unusedVariables false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
namespace PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
private lemma le_of_sq_le_sq_of_nonneg_sandwich_chart {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith
end PI.SwSandwichOfWork
end
end

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution (hN : NormRL) (hLI : LIso) {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r}
    (hv : v ∈ Vs k r) : ‖v‖ ≤ ‖Lm k r v‖ := by
  have h := (hLI k r).2.2 v hv
  simp only [hN k r] at h
  have hs : 0 ≤ ∑ a, ‖v.2.1 a‖ ^ 2 := Finset.sum_nonneg (fun a _ => by positivity)
  have hx1 : ‖v.2.1‖ ≤ Real.sqrt (∑ a, ‖v.2.1 a‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun a => ?_)
    calc ‖v.2.1 a‖ = Real.sqrt (‖v.2.1 a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ b, ‖v.2.1 b‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun b => ‖v.2.1 b‖ ^ 2)
          (fun b _ => by positivity) (Finset.mem_univ a))
  have hx : ‖v.2.1‖ ^ 2 ≤ ∑ a, ‖v.2.1 a‖ ^ 2 := by
    have hq := Real.sq_sqrt hs
    nlinarith [norm_nonneg v.2.1, Real.sqrt_nonneg (∑ a, ‖v.2.1 a‖ ^ 2)]
  have hL := norm_nonneg (Lm k r v)
  simp only [Prod.norm_def]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_)) <;> refine le_of_sq_le_sq_of_nonneg_sandwich_chart (norm_nonneg _) hL ?_ <;>
    nlinarith [sq_nonneg ‖v.1‖, sq_nonneg ‖v.2.1‖, sq_nonneg ‖v.2.2.1‖, sq_nonneg ‖v.2.2.2‖]
end PI.SwSandwichOfWork
