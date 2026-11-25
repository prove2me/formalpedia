-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_exists_near_91c44c1fd18c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:22.722902+00:00
-- url     : https://prove2.me/submissions/7fe07fc3-f55c-49b9-a1e6-c4e82dba9d35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PLatticeCount

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
open MeasureTheory Metric Module ZSpan
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (La : Submodule ℤ V) {c : ℝ}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace LatticeCount
theorem _root_.solution (B : ShortLatticeBasis La c) (x : V) :
    ∃ μ ∈ La, ‖x + μ‖ ≤ finrank ℝ V * c := by
  let e := basisOfLinearIndependentOfCardEqFinrank' B.vec B.linearIndependent (Fintype.card_fin _)
  have he : ∀ i, e i = B.vec i := fun i ↦ by simp [e]
  refine ⟨-((floor e x : Submodule.span ℤ (Set.range e)) : V), ?_, ?_⟩
  · refine La.neg_mem ?_
    have hle : Submodule.span ℤ (Set.range e) ≤ La := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact B.mem i
    exact hle (floor e x).2
  · rw [← sub_eq_add_neg, ← fract_apply]
    calc ‖fract e x‖ ≤ ∑ i, ‖e i‖ := norm_fract_le e x
      _ ≤ ∑ _i : Fin (finrank ℝ V), c :=
          Finset.sum_le_sum fun i _ ↦ by rw [he]; exact B.norm_le i
      _ = _ := by simp
end LatticeCount
end GroundTheory.Heights₂.Heights.HilbertSamuel
