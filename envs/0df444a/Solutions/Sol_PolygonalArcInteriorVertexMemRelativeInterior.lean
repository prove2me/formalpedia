-- Prove2me | solution 1 for PolygonalArcInteriorVertexMemRelativeInterior
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:02:05.196934+00:00
-- url     : https://prove2.me/submissions/393fc856-1b7d-48d1-b3a0-06fac8c97d65

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

theorem solution (γ : PolygonalArc)
    (i : Fin γ.vertices.length) (hpos : 0 < i.1)
    (hnext : i.1 + 1 < γ.vertices.length) :
    γ.vertices[i.1] ∈ γ.relativeInterior := by
  have hcarrier : γ.vertices[i.1] ∈ γ.carrier := by
    rw [γ.carrier_eq]
    exact ⟨i.1, hnext, left_mem_segment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1]⟩
  rw [γ.relativeInterior_eq]
  refine ⟨hcarrier, ?_⟩
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (hsource | htarget)
  · have h0lt : 0 < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      omega
    have hsource0 : γ.vertices[0] = γ.source := by
      have hget : γ.vertices[0]? = some γ.vertices[0] :=
        List.getElem?_eq_getElem h0lt
      rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
      exact Option.some.inj hget.symm
    have heq : γ.vertices[0] = γ.vertices[i.1] := by
      rw [hsource0, ← hsource]
    have hidx : 0 = i.1 := (γ.simple_vertices.getElem_inj_iff).mp heq
    omega
  · let last : ℕ := γ.vertices.length - 1
    have hlast_lt : last < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      dsimp [last]
      omega
    have htarget_last : γ.vertices[last] = γ.target := by
      have hlastEq := γ.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlastEq
      rw [List.getElem?_eq_getElem hlast_lt] at hlastEq
      exact Option.some.inj hlastEq
    have heq : γ.vertices[last] = γ.vertices[i.1] := by
      rw [htarget_last, ← htarget]
    have hidx : last = i.1 := (γ.simple_vertices.getElem_inj_iff).mp heq
    dsimp [last] at hidx
    omega
