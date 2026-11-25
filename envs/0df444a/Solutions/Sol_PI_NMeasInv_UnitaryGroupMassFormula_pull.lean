-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:11.021559+00:00
-- url     : https://prove2.me/submissions/af1f758c-36df-4668-9195-52c950ad824c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_map_comap_subgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
namespace PI.NMeasInv.UnitaryGroupMassFormula
section Abs
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
private theorem abs_inv_lemma (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G)
    (hνc : ν (S : Set G)ᶜ = 0) (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant := by
  have hemb : MeasurableEmbedding (Subtype.val : S → G) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hmc : (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := map_comap_subgroup S hS ν hνc
  refine ⟨fun s => ?_⟩
  have h1 : ((ν.comap (Subtype.val : S → G)).map (fun x : S => s * x)).map Subtype.val = ν := by
    rw [Measure.map_map hemb.measurable (measurable_const_mul s)]
    have hc : (Subtype.val ∘ fun x : S => s * x) = (fun y : G => (s : G) * y) ∘ Subtype.val := by
      funext x; simp
    rw [hc, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmc]
    exact hνi s s.2
  calc Measure.map (fun x : S => s * x) (ν.comap Subtype.val)
      = ((Measure.map (fun x : S => s * x) (ν.comap Subtype.val)).map Subtype.val).comap
          Subtype.val := (hemb.comap_map _).symm
    _ = ν.comap Subtype.val := by rw [h1]
end Abs
end PI.NMeasInv.UnitaryGroupMassFormula
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G) (hνc : ν (S : Set G)ᶜ = 0)
    (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) (hνf : IsFiniteMeasureOnCompacts ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (ν.comap (Subtype.val : S → G)) ∧
      (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
  have hemb : MeasurableEmbedding (Subtype.val : S → G) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  haveI := hνf
  refine ⟨abs_inv_lemma S hS ν hνc hνi, ⟨fun K hK => ?_⟩, map_comap_subgroup S hS ν hνc⟩
  rw [hemb.comap_apply]
  exact (hK.image continuous_subtype_val).measure_lt_top
end PI.NMeasInv.UnitaryGroupMassFormula
