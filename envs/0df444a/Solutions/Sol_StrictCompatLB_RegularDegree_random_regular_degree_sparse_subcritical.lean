-- Prove2me | solution 1 for StrictCompatLB.RegularDegree.random_regular_degree_sparse_subcritical
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T11:55:49.291558+00:00
-- url     : https://prove2.me/submissions/423b7bb7-3ecc-4aa6-b0c1-1f02be352778

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular
import Theorems.Thm_StrictCompatLB_RegularDegree_proposition_A_4
import Theorems.Thm_StrictCompatLB_RegularDegree_lemma_A_5
import Theorems.Thm_StrictCompatLB_RegularDegree_subcritical_of_A19

open Finset Filter MeasureTheory Topology

open StrictCompatLB.RegularDegree in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (d : ℕ) (hd : 2 ≤ d)
    (hc : Tendsto (fun N : ℕ => (c N : ℝ)) atTop atTop)
    (hcM_log : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / ((M N : ℝ) * Real.log (N : ℝ)))
      atTop atTop) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (randomGraph M adj ω) ∧
      StrictCompatLB.MeanField.IsSubcritical d M (randomGraph M adj ω) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNcM : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / (M N : ℝ)) atTop atTop := by
    refine (hcM_log.atTop_mul_atTop₀ hlog).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : Real.log (N : ℝ) ≠ 0 := by
      have : (1:ℝ) < N := by exact_mod_cast hN
      exact (Real.log_pos this).ne'
    have hM : (M N : ℝ) ≠ 0 := by
      have := (hc_pos N).trans (hcM N)
      exact_mod_cast (show M N ≠ 0 by omega)
    field_simp
  filter_upwards [proposition_A_4 P M c hc_pos hcM adj hadj hc hNcM,
    lemma_A_5 P M c hc_pos hcM adj hadj hcM_log] with ω h1 h2
  exact ⟨h1, subcritical_of_A19 d hd M _ h2⟩
