-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.range_congruenceSpecialToProjective_eq_PSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:24.036011+00:00
-- url     : https://prove2.me/submissions/3ba84512-45a2-4943-b896-052a2478045e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    (congruenceSpecialToProjective P r level).range = PSL P r level := by
  apply le_antisymm
  · rintro g ⟨a, rfl⟩
    exact ⟨indexSpecialLinearReduction P r level a, rfl⟩
  · rintro g ⟨s, rfl⟩
    obtain ⟨a, rfl⟩ := indexSpecialLinearMap_surjective P r level s
    exact ⟨a, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
