-- Prove2me | solution 1 for Plasticity.C0Sum.hasPlasticUnitBall_of_rank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:03.368742+00:00
-- url     : https://prove2.me/submissions/fd6d3110-1493-4d22-a69f-4580e6ad4f17

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorems.Thm_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two

/-!
Plasticity of the unit ball of a c₀ sum of blocks of dimension at most two: the case `E' = E`
of `Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two`.
-/

open Plasticity

theorem solution {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hE : ∀ i, Module.rank ℝ (E i) ≤ 2) : HasPlasticUnitBall (c0Sum E) :=
  fun f hf hb => Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two E E hE hE f hf hb
