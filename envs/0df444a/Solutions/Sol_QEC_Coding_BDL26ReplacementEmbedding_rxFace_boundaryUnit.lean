-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxFace_boundaryUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:51:31.180934+00:00
-- url     : https://prove2.me/submissions/9ff09afa-9854-46f9-bf3b-eb427bdac1de

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_planar
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_oldZ
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_pathStrip
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_terminalRung
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_boundaryRectangle
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_planar_boundaryUnit
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStrip_boundaryUnit
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStrip_boundaryUnit_upper
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldZ_boundaryUnit
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_terminalRung_boundaryUnit
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_boundaryRectangle_boundaryUnit
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section PointMaps
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
end PointMaps
noncomputable section TriangleFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end TriangleFrame
section AnchorGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end AnchorGeometry
noncomputable section WidthArea
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end WidthArea
section WidthPacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end WidthPacking
noncomputable section GridCornerBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end GridCornerBounds
section MaterializedSlots
end MaterializedSlots
noncomputable section ActualSlotCharging
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
private theorem rxFaceSlot_inverse_of_forward (P : TannerSquarePresentation) (S : OddScale)
    (actual : RXFace P S) (f : P.Face) (slot : PatchSlot S)
    (h : rxFaceSlotEquiv P S actual = (f, slot)) :
    (rxFaceSlotEquiv P S).symm (f, slot) = actual := by
  rw [← h, Equiv.symm_apply_apply]
end ActualSlotCharging
section ActualHitReindexing
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
end ActualHitReindexing
noncomputable section PathStripFineCoordinates
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
end PathStripFineCoordinates
noncomputable section PathStripUpperFineCoordinates
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
end PathStripUpperFineCoordinates
section LabeledTrianglePacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end LabeledTrianglePacking
noncomputable section PlanarFineCorners
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end PlanarFineCorners
noncomputable section IncomingTriangles
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end IncomingTriangles
section WidthPermutation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end WidthPermutation
noncomputable section ActualPositiveFaces
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualPositiveFaces
section ActualTriangleIndices
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualTriangleIndices
section FineTriangleAssignment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end FineTriangleAssignment
section FineHitMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end FineHitMetric
noncomputable section PositiveImageBridge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end PositiveImageBridge
section ActualPositiveWitness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualPositiveWitness
section ActualPositivePacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualPositivePacking
noncomputable section ActualPositiveSelection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualPositiveSelection
section ActualPositiveDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualPositiveDensity
section ActualFullDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualFullDensity
section RZDensityGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RZDensityGeometry
section RZDensityCount
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RZDensityCount
section FineEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end FineEdgeLength
section AdmissibleReplacementScale
end AdmissibleReplacementScale
section RoundedRZDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RoundedRZDensity
section FaceBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end FaceBoundaryUnit
section SeamBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end SeamBoundaryUnit
section AllFaceBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end AllFaceBoundaryUnit
section GlobalRXEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end GlobalRXEdgeLength
section GlobalRZEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end GlobalRZEdgeLength
section AffineBoundaryGluing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end AffineBoundaryGluing
noncomputable section ConstructedLocalMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ConstructedLocalMap
section RoundedConstructedLocalMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RoundedConstructedLocalMap
section ConstructedDegreeBounds
open BDL26BoundedValence
end ConstructedDegreeBounds
section CanonicalReplacementHandoff
open BDL26BoundedValence
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end CanonicalReplacementHandoff
noncomputable section IntrinsicLocalCompatibility
open BDL26DecodingGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end IntrinsicLocalCompatibility
section LocalFaceRestriction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end LocalFaceRestriction
section IntrinsicFaceDensity
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end IntrinsicFaceDensity
end QEC.Coding.BDL26ReplacementEmbedding
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (c : RXFace P S) : rxFaceBoundaryUnit P S J c := by
  obtain ⟨p, hp⟩ := (rxFaceSlotEquiv P S).symm.surjective c
  rcases p with ⟨f, slot⟩
  rw [← hp]
  rcases slot with (plane | ⟨side, i, copy, endpoint⟩) | (⟨side, edge, endpoint⟩ | copy)
  · rcases plane with ⟨⟨copy, i, j⟩, a, b⟩
    rw [rxFaceSlot_inverse_of_forward P S _ _ _ (rxFaceSlot_planar P S f i j copy a b)]
    exact planar_boundaryUnit P S J hgeo f i j copy a b
  · rw [rxFaceSlot_inverse_of_forward P S _ _ _
      (rxFaceSlot_boundaryRectangle P S f side copy i endpoint)]
    exact boundaryRectangle_boundaryUnit P S J hgeo f side copy i endpoint
  · rcases edge with ⟨copy, i⟩ | last
    · rw [rxFaceSlot_inverse_of_forward P S _ _ _
        (rxFaceSlot_pathStrip P S f side copy i endpoint)]
      fin_cases side
      · exact pathStrip_boundaryUnit P S J hgeo f copy i endpoint
      · exact pathStrip_boundaryUnit_upper P S J hgeo f copy i endpoint
    · have hl : last = 0 := Subsingleton.elim _ _
      subst last
      rw [rxFaceSlot_inverse_of_forward P S _ _ _
        (rxFaceSlot_terminalRung P S f side endpoint)]
      exact terminalRung_boundaryUnit P S J hgeo f side endpoint
  · rw [rxFaceSlot_inverse_of_forward P S _ _ _ (rxFaceSlot_oldZ P S f copy)]
    exact oldZ_boundaryUnit P S J hgeo f copy
end QEC.Coding.BDL26ReplacementEmbedding
