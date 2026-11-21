-- Prove2me | solution 1 for RiemannMasullo.one_mem_relativeRightHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:11:23.057959+00:00
-- url     : https://prove2.me/submissions/c4f2b571-b582-4f64-8c7a-21fb312661d9

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L156-L159
import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterRegions
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

theorem solution (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    1 ∈ relativeRightHalfPlane m hm hne a ↔ a < 0 := by
  change a < quasiCharacterAbscissa m hm hne 1 ↔ a < 0
  simp [quasiCharacterAbscissa]
