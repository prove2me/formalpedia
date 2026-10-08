-- Prove2me | solution 1 for Supermodularity.Games.equilibrium_iff_fixed_point_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:54:58.703152+00:00
-- url     : https://prove2.me/submissions/b6558aa8-8a03-408f-9b04-8bd80aa3d586

import Mathlib
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Games_BestJointResponse

open Supermodularity.Games in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x' : ∀ i, Fin (m i) → ℝ) :
    IsEquilibrium S f x' ↔ x' ∈ BestJointResponse S f x' := by
  constructor
  · rintro ⟨hS, h⟩ i
    refine ⟨by simpa [Function.update_eq_self] using hS, fun z hz => ?_⟩
    simpa [Function.update_eq_self] using h i z hz
  · intro h
    obtain ⟨i0⟩ := ‹Nonempty ι›
    have hS : x' ∈ S := by
      have := (h i0).1
      simpa [Function.update_eq_self] using this
    refine ⟨hS, fun i y hy => ?_⟩
    have := (h i).2 y hy
    simpa [Function.update_eq_self] using this
