-- Prove2me | solution 2 for QEC.Locality.edgeDivision_edges_cover
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:55.419701+00:00
-- url     : https://prove2.me/submissions/8dbf0f68-a803-43e2-805f-ce78ab40b72e

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active) :
    active.biUnion regions = directedEdgeFinset G := by
  obtain ⟨h1, h2, h3⟩ := hDivision
  ext e
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, he⟩
    exact h1 i hi he
  · intro he
    obtain ⟨i, ⟨hi, hei⟩, _⟩ := h3 e he
    exact ⟨i, hi, hei⟩
