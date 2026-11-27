-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_packing_example_4d57666d7620
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:22.153947+00:00
-- url     : https://prove2.me/submissions/1e0df08f-ba07-4bbc-bb5f-fefa21b23365

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt MeasureTheory Module Filter
  Topology Asymptotics Matrix
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution :
    let S : Finset (EuclideanSpace ℝ (Fin 2)) := {0, EuclideanSpace.basisFun (Fin 2) ℝ 0}
    (∀ s ∈ S, s ∈ standardLattice) ∧ (∀ s ∈ S, ‖s‖ ≤ 1) ∧
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Real.exp (-0) ≤ ‖s - t‖) ∧ S.card = 2 := by
  have hn : ‖EuclideanSpace.basisFun (Fin 2) ℝ 0‖ = 1 :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.1 0
  have hne : (0 : EuclideanSpace ℝ (Fin 2)) ≠ EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    intro h; rw [← h, norm_zero] at hn; exact zero_ne_one hn
  have hmem : EuclideanSpace.basisFun (Fin 2) ℝ 0 ∈ standardLattice :=
    Submodule.subset_span ⟨0, by simp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact Submodule.zero_mem _
    · rw [Finset.mem_singleton.mp hs]; exact hmem
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp
    · rw [Finset.mem_singleton.mp hs, hn]
  · intro s hs t ht hst
    rw [neg_zero, Real.exp_zero]
    rcases Finset.mem_insert.mp hs with rfl | hs <;> rcases Finset.mem_insert.mp ht with rfl | ht
    · exact absurd rfl hst
    · rw [Finset.mem_singleton.mp ht, zero_sub, norm_neg, hn]
    · rw [Finset.mem_singleton.mp hs, sub_zero, hn]
    · rw [Finset.mem_singleton.mp hs, Finset.mem_singleton.mp ht] at hst; exact absurd rfl hst
  · exact Finset.card_pair hne
end GroundTheory.Heights₂.Heights.HilbertSamuel
