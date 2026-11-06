-- Prove2me | solution 1 for ProbabilityTheory.hasStationaryIncrements_levyJumpProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T03:48:04.616942+00:00
-- url     : https://prove2.me/submissions/cd89afb0-3c92-4106-8a11-b892e734a02c

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Theorems.Thm_ProbabilityTheory_measurable_levyLargeJumpSum
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpProcess_sub
open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

theorem solution {Ω : Type} [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ}
    [SigmaFinite ν] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ)
    (hν : IsLevyMeasure ν) (b : ℝ) :
    HasStationaryIncrements (levyJumpProcess hd hν b) μ := by
  have haem : ∀ u : ℝ≥0, AEMeasurable (levyJumpProcess hd hν b u) μ := fun u =>
    (aemeasurable_const.add
      (measurable_levyLargeJumpSum hd.measurable_count hd.measurable_point).aemeasurable).add
      ((Lp.aestronglyMeasurable _).aemeasurable)
  have hcf : ∀ (s h : ℝ≥0) (ξ : ℝ),
      charFun (μ.map (increment (levyJumpProcess hd hν b) s (s + h))) ξ
        = Complex.exp (((h : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
    intro s h ξ
    rw [show increment (levyJumpProcess hd hν b) s (s + h)
        = fun ω => levyJumpProcess hd hν b (s + h) ω - levyJumpProcess hd hν b s ω from rfl,
      charFun_map_levyJumpProcess_sub hd hν b le_self_add ξ]
    congr 2
    push_cast
    ring
  intro s h
  have haem1 : AEMeasurable (increment (levyJumpProcess hd hν b) s (s + h)) μ :=
    (haem (s + h)).sub (haem s)
  have haem2 : AEMeasurable (increment (levyJumpProcess hd hν b) 0 h) μ :=
    (haem h).sub (haem 0)
  haveI : IsProbabilityMeasure (μ.map (increment (levyJumpProcess hd hν b) s (s + h))) :=
    Measure.isProbabilityMeasure_map haem1
  haveI : IsProbabilityMeasure (μ.map (increment (levyJumpProcess hd hν b) 0 h)) :=
    Measure.isProbabilityMeasure_map haem2
  refine ⟨haem1, haem2, Measure.ext_of_charFun (funext fun ξ => ?_)⟩
  rw [hcf s h ξ]
  have := hcf 0 h ξ
  rw [zero_add] at this
  rw [this]