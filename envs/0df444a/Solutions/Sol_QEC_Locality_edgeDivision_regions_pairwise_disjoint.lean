-- Prove2me | solution 1 for QEC.Locality.edgeDivision_regions_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:13:24.111525+00:00
-- url     : https://prove2.me/submissions/06924e1c-3a66-4166-8f19-9aaf07897b6e

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    Disjoint (regions i) (regions j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro edge hiedge hjedge
  have hedge : edge ∈ directedEdgeFinset G := hDivision.1 i hi hiedge
  rcases hDivision.2.2 edge hedge with ⟨owner, _, howner⟩
  have hiOwner : i = owner := howner i ⟨hi, hiedge⟩
  have hjOwner : j = owner := howner j ⟨hj, hjedge⟩
  exact hij (hiOwner.trans hjOwner.symm)
end QEC.Locality
