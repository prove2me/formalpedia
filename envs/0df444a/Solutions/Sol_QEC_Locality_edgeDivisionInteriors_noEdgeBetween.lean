-- Prove2me | solution 1 for QEC.Locality.edgeDivisionInteriors_noEdgeBetween
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:24.190625+00:00
-- url     : https://prove2.me/submissions/b20fb691-23b0-434d-800b-be0375534668

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff
import Theorems.Thm_QEC_Locality_mem_edgeIncidentVertices_iff
import Theorems.Thm_QEC_Locality_mem_edgeDivisionSharedBoundary_iff
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

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
theorem _root_.solution {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    NoEdgeBetween G (edgeDivisionInterior regions active i)
      (edgeDivisionInterior regions active j) := by
  classical
  intro x hxi y hyj hxy
  have hedge : (x, y) ∈ directedEdgeFinset G :=
    (mem_directedEdgeFinset_iff G x y).2 hxy
  rcases (hDivision.2.2 (x, y) hedge) with ⟨k, ⟨hk, hkedge⟩, _⟩
  have endpoints := endpoint_mem_edgeIncidentVertices regions hkedge
  have hki := interior_incident_region_unique regions active hi hk hxi endpoints.1
  have hkj := interior_incident_region_unique regions active hj hk hyj endpoints.2
  exact hij (hki.symm.trans hkj)
end QEC.Locality
