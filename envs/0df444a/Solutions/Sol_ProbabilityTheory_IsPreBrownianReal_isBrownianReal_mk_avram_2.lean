-- Prove2me | solution 2 for ProbabilityTheory.IsPreBrownianReal.isBrownianReal_mk_avram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:35:52.202313+00:00
-- url     : https://prove2.me/submissions/38cb44b7-8291-47e6-b61b-f842d8621f09

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Mathlib.Tactic

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (h : ProbabilityTheory.IsPreBrownianReal X P) :
    ProbabilityTheory.IsBrownianReal (h.mk X) P := by
  have hs := h.exists_continuous_modification.choose_spec
  refine ⟨h.congr (fun t => (hs.2.1 t).symm), Filter.Eventually.of_forall fun ω => ?_⟩
  rw [continuous_iff_continuousAt]
  intro t
  have hb : BddAbove (Set.range fun n : ℕ => (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [div_le_one (by positivity)]
    push_cast; linarith
  have hβ : ((1/5 : ℝ≥0) : ℝ) < ⨆ n : ℕ, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) := by
    refine lt_of_lt_of_le ?_ (le_ciSup hb 0)
    norm_num
  obtain ⟨U, hU, C, hH⟩ := hs.2.2 ω t (1/5) (by norm_num) hβ
  exact (hH.continuousOn (by norm_num)).continuousAt hU
