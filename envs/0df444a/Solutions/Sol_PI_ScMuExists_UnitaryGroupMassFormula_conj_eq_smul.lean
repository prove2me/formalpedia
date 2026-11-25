-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.conj_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:54.296339+00:00
-- url     : https://prove2.me/submissions/b0d48794-7c56-4768-81d5-526a51f399db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_continuous_conjSub
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_continuous_conjSub_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (N : Subgroup G) (hN : IsClosed (N : Set G)) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) :
    ∃ c : ℝ≥0, (haarSub N hN).map (fun x => g * x * g⁻¹) = c • haarSub N hN := by
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := by
    first
      | exact TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
      | exact Topology.IsInducing.subtypeVal.secondCountableTopology
      | exact inducing_subtype_val.secondCountableTopology
      | infer_instance
  have hφc := continuous_conjSub N g h1 h2
  have hφs := continuous_conjSub_symm N g h1 h2
  haveI := MulEquiv.isHaarMeasure_map (Measure.haar : Measure N) (conjSub N g h1 h2) hφc hφs
  refine ⟨Measure.haarScalarFactor ((Measure.haar : Measure N).map (conjSub N g h1 h2)) Measure.haar, ?_⟩
  have hc : Measurable (fun x : G => g * x * g⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hcomp : (fun x : G => g * x * g⁻¹) ∘ (Subtype.val : N → G) = Subtype.val ∘ (conjSub N g h1 h2) :=
    rfl
  unfold haarSub
  rw [Measure.map_map hc measurable_subtype_coe, hcomp,
    ← Measure.map_map measurable_subtype_coe hφc.measurable]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul ((Measure.haar : Measure N).map (conjSub N g h1 h2))
    Measure.haar]
  rw [Measure.map_smul]
end PI.ScMuExists.UnitaryGroupMassFormula
