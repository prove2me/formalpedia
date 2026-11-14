-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_seed_is_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:50:38.198198+00:00
-- url     : https://prove2.me/submissions/710b26d8-8dd1-4eb3-b7aa-968a16c6c48c

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (bijunctiveSeedMeasure rep I ε) := by
  have hunit : IsProbabilityMeasure unitPriorityMeasure := by
    unfold unitPriorityMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
  have hcut : IsProbabilityMeasure (cutoffMeasure ε) := by
    unfold cutoffMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
  have hβ : 0 < bijunctiveRate rep ε := by
    unfold bijunctiveRate
    apply div_pos hε
    have hh : (0 : ℝ) < rep.clauseBound := by exact_mod_cast rep.clauseBound_pos
    positivity
  have hshift : IsProbabilityMeasure (shiftMeasure (bijunctiveRate rep ε)) := by
    exact isProbabilityMeasure_expMeasure hβ
  letI : IsProbabilityMeasure unitPriorityMeasure := hunit
  letI : IsProbabilityMeasure (cutoffMeasure ε) := hcut
  letI : IsProbabilityMeasure (shiftMeasure (bijunctiveRate rep ε)) := hshift
  unfold bijunctiveSeedMeasure
  infer_instance
