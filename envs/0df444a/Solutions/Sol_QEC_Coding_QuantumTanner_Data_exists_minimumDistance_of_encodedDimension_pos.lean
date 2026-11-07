-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.exists_minimumDistance_of_encodedDimension_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:14:49.329038+00:00
-- url     : https://prove2.me/submissions/8b93e4ef-1cb8-4ee0-ad8d-0a069f9137f8

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_encodedDimension_eq
import Theorems.Thm_QEC_Coding_exists_algebraicCSSMinimumDistance_of_exists_logical


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.Data
open Classical
universe v
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (D : Data G A B Square XBasis ZBasis) (hPositive : 0 < D.encodedDimension) :
    ∃ distance : Nat, AlgebraicCSSMinimumDistance
      D.chainComplex.firstCoboundaryCheckCode D.chainComplex.middleBoundaryCode distance := by
  have hWitness : ∃ x : Word (ZMod 2) Square,
      x ∈ D.chainComplex.middleCycleCode.carrier ∧
        x ∉ D.chainComplex.middleBoundaryCode.carrier := by
    by_contra h
    have hLe : D.chainComplex.middleCycleCode.carrier ≤
        D.chainComplex.middleBoundaryCode.carrier := by
      intro x hx
      by_contra hn
      exact h ⟨x, hx, hn⟩
    have hEq := le_antisymm hLe D.chainComplex.middleBoundaryCode_le_middleCycleCode
    rw [D.encodedDimension_eq, Dimension_eq_finrank_carrier,
      Dimension_eq_finrank_carrier, hEq, Nat.sub_self] at hPositive
    omega
  obtain ⟨x, hx, hn⟩ := hWitness
  apply exists_algebraicCSSMinimumDistance_of_exists_logical
  exact ⟨x, Or.inr ⟨by
    rw [D.chainComplex.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
    exact hx, hn⟩⟩
end QEC.Coding.QuantumTanner.Data
