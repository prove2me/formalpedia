-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.PSL_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:25.155106+00:00
-- url     : https://prove2.me/submissions/20554d41-3fc1-45a7-bcdf-e42f7a9a5b4d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_natCard_residueField_le_natCard_PSL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueField_unbounded


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
theorem _root_.solution (P : BasePrime) (r : Rank) (bound : Nat) :
    ∃ level, bound < Nat.card (PSL P r level) := by
  obtain ⟨level, hlevel⟩ := residueField_unbounded P r bound
  exact ⟨level, hlevel.trans_le
    (natCard_residueField_le_natCard_PSL P r level)⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
