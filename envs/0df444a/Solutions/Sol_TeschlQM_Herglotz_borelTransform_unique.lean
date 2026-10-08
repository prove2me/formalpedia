-- Prove2me | solution 1 for TeschlQM.Herglotz.borelTransform_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T05:49:13.240814+00:00
-- url     : https://prove2.me/submissions/3ab24690-d79f-4a43-84d8-b20912d37b49

import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_TeschlQM_Herglotz_stieltjes_inversion_formula
import Theorems.Thm_MeasureTheory_Measure_eq_of_interval_average
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set
open scoped Topology

namespace HerglotzStieltjes


end HerglotzStieltjes

open HerglotzStieltjes

theorem solution (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : ℂ, 0 < z.im →
      TeschlQM.Herglotz.borelTransform μ z = TeschlQM.Herglotz.borelTransform ν z) : μ = ν := by
  apply MeasureTheory.Measure.eq_of_interval_average
  intro a b hab
  have he : (fun ε : ℝ => (1 / Real.pi) * (∫ t in a..b,
      (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => (1 / Real.pi) * (∫ t in a..b,
      (TeschlQM.Herglotz.borelTransform ν ((t : ℂ) + (ε : ℂ) * Complex.I)).im)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    change (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im = _
    rw [h _ (by simpa using hε)]
  exact tendsto_nhds_unique (TeschlQM.Herglotz.stieltjes_inversion_formula μ a b hab)
    ((TeschlQM.Herglotz.stieltjes_inversion_formula ν a b hab).congr' he.symm)

