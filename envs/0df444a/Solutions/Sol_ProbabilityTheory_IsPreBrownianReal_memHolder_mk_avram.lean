-- Prove2me | solution 1 for ProbabilityTheory.IsPreBrownianReal.memHolder_mk_avram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:27:17.979078+00:00
-- url     : https://prove2.me/submissions/8be62158-4d1d-46f5-b7d4-bafbe2a5452d

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Mathlib.Tactic

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (h : ProbabilityTheory.IsPreBrownianReal X P)
    (ω : Ω) (t : ℝ≥0) (β : ℝ≥0)
    (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (h.mk X · ω) U := by
  have hs := h.exists_continuous_modification.choose_spec.2.2
  refine hs ω t β hβ_pos ?_
  have hb : BddAbove (Set.range fun n : ℕ => (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [div_le_one (by positivity)]
    push_cast; linarith
  have hβ' : (β : ℝ) < 1 / 2 := by
    have : (β : ℝ) < ((2⁻¹ : ℝ≥0) : ℝ) := by exact_mod_cast hβ_lt
    simpa using this
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - 2 * (β : ℝ)))
  refine lt_of_lt_of_le ?_ (le_ciSup hb n)
  have h1 : 0 < 1 - 2 * (β : ℝ) := by linarith
  have h2 : 1 < (1 - 2 * (β : ℝ)) * n := by
    rw [div_lt_iff₀ h1] at hn; linarith
  rw [lt_div_iff₀ (by positivity)]
  push_cast
  nlinarith
