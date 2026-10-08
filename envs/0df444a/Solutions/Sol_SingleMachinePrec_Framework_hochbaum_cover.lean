-- Prove2me | solution 1 for SingleMachinePrec.Framework.hochbaum_cover
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:08:57.871729+00:00
-- url     : https://prove2.me/submissions/9a16f236-f1f0-4112-acd4-dc079798edee

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP

set_option autoImplicit false

open SingleMachinePrec.Framework in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] (S : Instance N)
    (x : IncPair S.P → ℝ) (hx : IsCSLPFeasible S x) (hhalf : IsHalfIntegral x)
    (C : Finset (IncPair S.P)) (hCsub : C ⊆ levelSet x (1 / 2))
    (hC : ((vertexCoverGraph S.P).induce (levelSet x (1 / 2) : Set (IncPair S.P))).IsVertexCover
      {v | v.1 ∈ C}) :
    (vertexCoverGraph S.P).IsVertexCover ((levelSet x 1 ∪ C : Finset (IncPair S.P)) : Set _) := by
  intro u v huv
  have hsum := hx.2 u v huv
  have hmem : ∀ w a, w ∈ levelSet x a ↔ x w = a := by
    intro w a
    simp [levelSet]
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
  rcases hhalf u with hu | hu | hu
  · rcases hhalf v with hv | hv | hv
    · rw [hu, hv] at hsum; norm_num at hsum
    · rw [hu, hv] at hsum; norm_num at hsum
    · exact Or.inr (Or.inl ((hmem v 1).2 hv))
  · rcases hhalf v with hv | hv | hv
    · rw [hu, hv] at hsum; norm_num at hsum
    · have hu' : u ∈ levelSet x (1 / 2) := (hmem u _).2 hu
      have hv' : v ∈ levelSet x (1 / 2) := (hmem v _).2 hv
      have hadj : ((vertexCoverGraph S.P).induce
          (levelSet x (1 / 2) : Set (IncPair S.P))).Adj ⟨u, hu'⟩ ⟨v, hv'⟩ := by
        simpa using huv
      rcases hC hadj with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ((hmem v 1).2 hv))
  · exact Or.inl (Or.inl ((hmem u 1).2 hu))
