-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:36:24.38377+00:00
-- url     : https://prove2.me/submissions/b9fa2c3d-c536-46a7-b4b7-e9b260461f67

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

open TwoStageSRO.AsymOpt in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (PiC : Set (Pol d r))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : ℝ) (s : ℕ → Fin d → ℝ) (N : ℕ) :
    (vSRO M p ε s N ≤ vMP M PiC p ε s N ∧ vMP M PiC p ε s N ≤ vSP M PiC p ε s N) ∧
    ∀ x : Fin n → ℝ,
      VSRO M p ε s N x ≤ VMP M PiC p ε s N x ∧ VMP M PiC p ε s N x ≤ VSP M PiC p ε s N x := by
  have hN : (0 : EReal) ≤ (((N : ℝ)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg N)
  have key : ∀ x : Fin n → ℝ,
      VSRO M p ε s N x ≤ VMP M PiC p ε s N x ∧ VMP M PiC p ε s N x ≤ VSP M PiC p ε s N x := by
    intro x
    constructor
    · unfold VMP
      refine le_iInf₂ fun ys hys => ?_
      unfold VSRO
      gcongr
      rw [Finset.sum_range (fun i => ⨆ ζ ∈ U M p ε s i, Q M x ζ)]
      refine Finset.sum_le_sum fun i _ => ?_
      unfold robCost
      refine iSup₂_le fun ζ hζ => ?_
      refine le_iSup₂_of_le ζ hζ ?_
      unfold Q
      exact sInf_le ⟨ys i ζ, (hys i).2 ζ hζ, rfl⟩
    · unfold VSP
      refine le_iInf₂ fun y hy => ?_
      unfold VMP
      refine iInf₂_le_of_le (fun _ => y) ?_ ?_
      · intro i
        refine ⟨hy.1, fun ζ hζ => hy.2 ζ ?_⟩
        exact Set.mem_biUnion (Finset.mem_range.mpr i.2) hζ
      · rw [Finset.sum_range (fun i => robCost M (U M p ε s i) y)]
  refine ⟨⟨?_, ?_⟩, key⟩
  · exact iInf_mono fun x => (key x).1
  · exact iInf_mono fun x => (key x).2
