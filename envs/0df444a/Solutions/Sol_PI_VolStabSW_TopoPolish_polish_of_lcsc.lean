-- Prove2me | solution 1 for PI.VolStabSW.TopoPolish.polish_of_lcsc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:43.481419+00:00
-- url     : https://prove2.me/submissions/cdb6ae7c-640d-450c-969b-4f1b5516dd52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoPolish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.TopoPolish
open Topology TopologicalSpace Set
namespace PI.VolStabSW.TopoPolish
theorem _root_.solution (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  letI := TopologicalSpace.metrizableSpaceMetric Y
  have hemb : IsEmbedding ((↑) : Y → UniformSpace.Completion Y) :=
    (UniformSpace.Completion.isUniformEmbedding_coe Y).isEmbedding
  have hdense : DenseRange ((↑) : Y → UniformSpace.Completion Y) :=
    UniformSpace.Completion.denseRange_coe
  have hopen : IsOpen (range ((↑) : Y → UniformSpace.Completion Y)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, rfl⟩
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨V, hVK, hVo, hyV⟩ := mem_nhds_iff.1 hKy
    obtain ⟨U, hUo, hUV⟩ := hemb.isInducing.isOpen_iff.1 hVo
    refine ⟨U, ?_, hUo, ?_⟩
    · have hcl : IsClosed (((↑) : Y → UniformSpace.Completion Y) '' K) :=
        (hK.image hemb.continuous).isClosed
      calc U ⊆ closure (U ∩ range ((↑) : Y → UniformSpace.Completion Y)) :=
            hdense.open_subset_closure_inter hUo
        _ ⊆ closure (((↑) : Y → UniformSpace.Completion Y) '' K) := by
            apply closure_mono
            rintro _ ⟨hz, ⟨z, rfl⟩⟩
            refine ⟨z, hVK ?_, rfl⟩
            rw [← hUV]
            exact hz
        _ = ((↑) : Y → UniformSpace.Completion Y) '' K := hcl.closure_eq
        _ ⊆ range ((↑) : Y → UniformSpace.Completion Y) := image_subset_range _ _
    · show y ∈ ((↑) : Y → UniformSpace.Completion Y) ⁻¹' U
      rw [hUV]
      exact hyV
  have : PolishSpace (range ((↑) : Y → UniformSpace.Completion Y)) := hopen.polishSpace
  exact hemb.toHomeomorph.isClosedEmbedding.polishSpace
end PI.VolStabSW.TopoPolish
