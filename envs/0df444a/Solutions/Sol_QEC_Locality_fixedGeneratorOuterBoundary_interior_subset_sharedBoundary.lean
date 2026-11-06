-- Prove2me | solution 1 for QEC.Locality.fixedGeneratorOuterBoundary_interior_subset_sharedBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:22:38.701536+00:00
-- url     : https://prove2.me/submissions/65169384-3bec-48f2-9139-53b7a927b107

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff
import Theorems.Thm_QEC_Locality_mem_edgeIncidentVertices_iff
import Theorems.Thm_QEC_Locality_mem_edgeDivisionSharedBoundary_iff
import Theorems.Thm_QEC_Locality_mem_fixedGeneratorOuterBoundaryFinset_iff

section
namespace QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] in
private theorem endpoint_mem_edgeIncidentVertices {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) {i : m} {x y : ι}
    (hedge : (x, y) ∈ regions i) :
    x ∈ edgeIncidentVertices (regions i) ∧
      y ∈ edgeIncidentVertices (regions i) := by
  constructor
  · exact (mem_edgeIncidentVertices_iff (regions i) x).2
      ⟨(x, y), hedge, Or.inl rfl⟩
  · exact (mem_edgeIncidentVertices_iff (regions i) y).2
      ⟨(x, y), hedge, Or.inr rfl⟩
private theorem interior_incident_region_unique {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m)
    {i k : m} (hi : i ∈ active) (hk : k ∈ active) {x : ι}
    (hxi : x ∈ edgeDivisionInterior regions active i)
    (hxk : x ∈ edgeIncidentVertices (regions k)) : k = i := by
  classical
  by_contra hki
  have hxi' := Finset.mem_sdiff.mp hxi
  exact hxi'.2 ((mem_edgeDivisionSharedBoundary_iff regions active x).2
    ⟨i, hi, k, hk, Ne.symm hki, hxi'.1, hxk⟩)
end QEC.Locality
end

set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    {i : m} (hi : i ∈ active) :
    fixedGeneratorOuterBoundaryFinset P (edgeDivisionInterior regions active i) ⊆
      edgeDivisionSharedBoundary regions active := by
  classical
  intro y hy
  rw [mem_fixedGeneratorOuterBoundaryFinset_iff] at hy
  rcases hy with ⟨hyInterior, x, hxi, hxy⟩
  have hedge : (x, y) ∈ directedEdgeFinset P.fixedGeneratorInteractionGraph :=
    (mem_directedEdgeFinset_iff _ x y).2 hxy
  rcases hDivision.2.2 (x, y) hedge with ⟨k, ⟨hk, hkedge⟩, _⟩
  have endpoints := endpoint_mem_edgeIncidentVertices regions hkedge
  have hki := interior_incident_region_unique regions active hi hk hxi endpoints.1
  subst k
  by_contra hyShared
  apply hyInterior
  exact Finset.mem_sdiff.mpr ⟨endpoints.2, hyShared⟩
end QEC.Locality
