-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.source_u_transported_reference_boundary_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/216763ea-2351-4845-8d10-d25f2ee91304

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_transported_partition_boundary_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceProductThroughAlpha
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (QΓ : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (QΓ n).parts,
          (SoficGroups.boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)).parts,
          (SoficGroups.boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                  SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement *
                (A.model n).action
                  (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i) *
                  ((A.model n).action
                    SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
            C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0) := by
  have h :=
    SoficGroups.KunTransportedAmbientOverlap.transported_partition_boundary_density_tendsto_zero
      (V := fun n => Fin (A.model n).size)
      QΓ
      (fun n (i : ↥SΓ) =>
        (A.model n).action
          (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion i))
      (fun n =>
        (A.model n).action
          SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)
      (by simpa only [Fintype.card_fin] using hboundary)
  simpa only [Fintype.card_fin] using h
end SoficGroups.SourceProductThroughAlpha
