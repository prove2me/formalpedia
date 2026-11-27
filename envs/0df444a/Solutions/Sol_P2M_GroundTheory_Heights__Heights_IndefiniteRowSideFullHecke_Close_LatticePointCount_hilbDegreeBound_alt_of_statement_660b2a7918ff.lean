-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LatticePointCount_hilbDegreeBound_alt_of_statement_660b2a7918ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:56:11.008383+00:00
-- url     : https://prove2.me/submissions/3708e757-3194-470e-90a8-aec25e80b0ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_HilbDegreeBoundAltOfStatement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LatticePointCount_log_error_le_303c1986598d

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace LatticePointCount
theorem _root_.solution (hA : GroundTheory.Heights₂.Heights.LatticePointCount.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LatticePointCount.Statement := by
  intro C hC
  refine ⟨1 + Real.log (2 * (1 + C)) / Real.log 2, ?_⟩
  intro E _ _ r b hb S hS hcl
  have hmem : ∀ x : E, x ∈ AddSubgroup.closure (Set.range b) ↔ x ∈ Submodule.span ℤ (Set.range b) :=
    fun x ↦ by rw [← Submodule.span_int_eq_addSubgroupClosure]; exact Submodule.mem_toAddSubgroup _
  have hspan : Submodule.span ℤ (S : Set E) = Submodule.span ℤ (Set.range b) :=
    Submodule.toAddSubgroup_injective (by
      rw [Submodule.span_int_eq_addSubgroupClosure, Submodule.span_int_eq_addSubgroupClosure, hcl])
  have hset : {x : E | x ∈ AddSubgroup.closure (Set.range b) ∧ ‖x‖ ≤ 1} =
      {x : E | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, hmem]
  obtain ⟨hfin, hlog⟩ := hA E r b hb (S : Set E) C hC.le hS hspan
  have hnn : 0 ≤ gram b := by
    unfold gram
    exact (Matrix.posSemidef_gram ℝ b).det_nonneg
  have hg : -Real.log (Real.sqrt (gram b)) =
      -(1 / 2) * Real.log (Matrix.of fun i j ↦ @inner ℝ E _ (b i) (b j)).det := by
    rw [Real.log_sqrt hnn]
    unfold gram
    ring
  rw [hset]
  refine ⟨hfin, ?_⟩
  rw [hg]
  have := LatticePointCount.log_error_le hC.le r
  linarith
end LatticePointCount
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
