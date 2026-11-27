-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_HadamardGramBound_equiv_9500bfbb99cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:04:30.40466+00:00
-- url     : https://prove2.me/submissions/7e30fc2e-e269-4d41-a2b3-2fea7308d134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LinearIndependentOfMemSpan
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_HadamardGramBound_linearIndependent_of_mem_span_a89d91bbfa19

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound
theorem _root_.solution : GroundTheory.Heights₂.Heights.HadamardGramBound.Statement ↔
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound.Statement := by
  constructor
  · intro hA E _ _ r v hv hn
    have key : ∀ b : Fin r → E, (∀ i, v i ∈ Submodule.span ℤ (Set.range b)) →
        0 ≤ -Real.log (Real.sqrt (gram b)) := by
      intro b hb
      obtain ⟨_, h1⟩ := hA E r v b hv hn hb
      rw [neg_nonneg]
      have h1' : gram b ≤ 1 := h1
      refine Real.log_nonpos (Real.sqrt_nonneg _) ?_
      simpa using Real.sqrt_le_sqrt h1'
    refine ⟨key v fun i ↦ Submodule.subset_span ⟨i, rfl⟩, fun b _ hb ↦ key b fun i ↦ ?_⟩
    have h := hb i
    rwa [← Submodule.span_int_eq_addSubgroupClosure] at h
  · intro hB V _ _ r v b hv hn hb
    have hbli := linearIndependent_of_mem_span v b hv hb
    have hpos : 0 < gram b := (Matrix.posDef_gram_of_linearIndependent hbli).det_pos
    have h := (hB V r v hv hn).2 b hbli fun i ↦ by
      rw [← Submodule.span_int_eq_addSubgroupClosure]
      exact hb i
    rw [neg_nonneg, Real.log_nonpos_iff (Real.sqrt_nonneg _),
      Real.sqrt_le_left zero_le_one, one_pow] at h
    exact ⟨hpos, h⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound
