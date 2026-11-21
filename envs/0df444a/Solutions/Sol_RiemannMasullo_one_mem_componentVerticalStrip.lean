-- Prove2me | solution 1 for RiemannMasullo.one_mem_componentVerticalStrip
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:11:23.761148+00:00
-- url     : https://prove2.me/submissions/e3bcf051-c13f-4901-af9b-0ae58d447b62

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L163-L165
import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterRegions
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

theorem solution (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    1 ∈ componentVerticalStrip m hm hne 1 I ↔ 0 ∈ I := by
  simp [componentVerticalStrip, relativeVerticalStrip, quasiCharacterAbscissa, normOneRestriction]
