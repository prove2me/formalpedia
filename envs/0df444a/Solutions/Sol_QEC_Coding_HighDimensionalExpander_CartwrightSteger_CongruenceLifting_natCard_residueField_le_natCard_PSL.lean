-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.natCard_residueField_le_natCard_PSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:44:16.839676+00:00
-- url     : https://prove2.me/submissions/bb322c8a-b49a-48b9-ba63-7b2a536310ad

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionPSL_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card (ResidueField P r level) ≤
      Nat.card (PSL P r level) := by
  classical
  let projectToPSL :
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ResidueField P r level) →
        PSL P r level := fun s =>
    ⟨specialToProjective P r level s, ⟨s, rfl⟩⟩
  have projectToPSL_surjective : Function.Surjective projectToPSL := by
    rintro ⟨g, s, rfl⟩
    exact ⟨s, rfl⟩
  letI : Finite (PSL P r level) :=
    Finite.of_surjective projectToPSL projectToPSL_surjective
  exact Nat.card_le_card_of_injective
    (residueTransvectionPSL P r level)
    (residueTransvectionPSL_injective P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
