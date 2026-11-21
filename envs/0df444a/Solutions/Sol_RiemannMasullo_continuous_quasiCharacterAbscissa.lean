-- Prove2me | solution 1 for RiemannMasullo.continuous_quasiCharacterAbscissa
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:49:08.08163+00:00
-- url     : https://prove2.me/submissions/b6688619-81d8-497f-a995-957719ab2eeb

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L122-L127
import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

theorem solution (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Continuous (quasiCharacterAbscissa m hm hne) := by
  have hev : Continuous (fun c : QuasiCharacter G => c hne.choose) := continuous_eval_const _
  have hneval (c : QuasiCharacter G) : c hne.choose ≠ 0 :=
    ((Group.isUnit hne.choose).map c).ne_zero
  exact (hev.norm.log fun c => norm_ne_zero_iff.mpr (hneval c)).div_const _
