-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_eq_restrict_0ba29adf8ab5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:47.297364+00:00
-- url     : https://prove2.me/submissions/4d216363-65ed-4283-93f0-6794c11b0534

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_preimage_univ_prod_19221bf5a91f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_preimage_prod_eq_c1495817f774

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
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (hV : IsOpen V) (A : Set G₁) :
    μ (Φ ⁻¹' (A ×ˢ V)) = μ.restrict (Φ ⁻¹' (univ ×ˢ V)) ((fun x => (Φ x).1) ⁻¹' A) := by
  rw [Measure.restrict_apply' (measurableSet_preimage_univ_prod hV), preimage_prod_eq]
end GroundTheory.Heights₂.Heights.FiniteCovolume
