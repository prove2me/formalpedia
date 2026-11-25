-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_quasiMeasurePreserving_fst_comp_d334dff1b519
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:36.934827+00:00
-- url     : https://prove2.me/submissions/7ceea013-a27e-43a9-8fa1-ca38cace33f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_fst_comp_ffba65d6ed46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_eq_smul_haar_b8209152515f

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
    Measure.QuasiMeasurePreserving (fun x => (Φ x).1) (μ.restrict (Φ ⁻¹' (univ ×ˢ V)))
      (Measure.haar : Measure G₁) := by
  refine ⟨measurable_fst_comp Φ, fun A hA => ?_⟩
  change sliceMeasure Φ μ V A = 0
  obtain ⟨c, hc⟩ := sliceMeasure_eq_smul_haar (Φ := Φ) (μ := μ) hV hVc
  rw [hc, Measure.smul_apply, hA, smul_zero]
end GroundTheory.Heights₂.Heights.FiniteCovolume
