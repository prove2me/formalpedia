-- Prove2me | solution 2 for QEC.Locality.edgeDivision_regions_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:30:04.274716+00:00
-- url     : https://prove2.me/submissions/6013f2c3-ac32-4c95-8bbd-26b14873a3a7

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem solution {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    Disjoint (regions i) (regions j) := by
  obtain ⟨h1, h2, h3⟩ := hDivision
  rw [Finset.disjoint_left]
  intro e hei hej
  have hd := h1 i hi hei
  obtain ⟨k, _, huniq⟩ := h3 e hd
  exact hij ((huniq i ⟨hi, hei⟩).trans (huniq j ⟨hj, hej⟩).symm)
