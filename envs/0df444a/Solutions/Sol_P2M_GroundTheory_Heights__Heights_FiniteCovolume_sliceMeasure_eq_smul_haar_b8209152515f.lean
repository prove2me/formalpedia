-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_eq_smul_haar_b8209152515f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:30.486806+00:00
-- url     : https://prove2.me/submissions/fe3a027d-dc9b-4bec-beb9-c721706f405a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_isMulLeftInvariant_74f2e0b9f507
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_isFiniteMeasureOnCompacts_0ebe71c42548

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
set_option linter.unusedSectionVars false
noncomputable section
variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}
variable [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [μ.IsHaarMeasure]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (hV : IsOpen V) (hVc : IsCompact V) :
    ∃ c : ℝ≥0, sliceMeasure Φ μ V = c • Measure.haar := by
  have := sliceMeasure_isMulLeftInvariant (Φ := Φ) (μ := μ) hV
  have := sliceMeasure_isFiniteMeasureOnCompacts (Φ := Φ) (μ := μ) hV hVc
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
end GroundTheory.Heights₂.Heights.FiniteCovolume
