-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.map_comap_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:52.064725+00:00
-- url     : https://prove2.me/submissions/bd07654a-04bf-4376-93c1-f96eb41adf67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G)
    (hc : μ (H : Set G)ᶜ = 0) : (μ.comap ((↑) : H → G)).map ((↑) : H → G) = μ := by
  have hemb : MeasurableEmbedding ((↑) : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  ext s hs
  rw [Measure.map_apply hemb.measurable hs, hemb.comap_apply, Set.image_preimage_eq_inter_range]
  have hr : Set.range ((↑) : H → G) = (H : Set G) := by ext x; simp
  rw [hr]
  have h1 := measure_inter_add_diff (μ := μ) s hH.measurableSet
  have h2 : μ (s \ (H : Set G)) = 0 := measure_mono_null (fun x hx => hx.2) hc
  rw [h2, add_zero] at h1
  exact h1
end PI.NMeasInv.UnitaryGroupMassFormula
