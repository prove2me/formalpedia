-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.blockLength_le_encodedDimension_add_checks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:14:38.584092+00:00
-- url     : https://prove2.me/submissions/bd496af9-880c-4392-8848-504fba56ad2b

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_encodedDimension_eq


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
    (D : Data G A B Square XBasis ZBasis) :
    D.blockLength ≤ D.encodedDimension +
      Fintype.card G * (Fintype.card XBasis + Fintype.card ZBasis) := by
  have hNull := D.chainComplex.boundary1.finrank_range_add_finrank_ker
  have hFirst := Submodule.finrank_le (LinearMap.range D.chainComplex.boundary1)
  have hSecond := D.chainComplex.boundary2.finrank_range_le
  have hBoundary := Submodule.finrank_mono D.chainComplex.middleBoundaryCode_le_middleCycleCode
  rw [finrank_word_eq_length, Length] at hNull hFirst hSecond
  rw [Fintype.card_prod] at hFirst hSecond
  rw [D.encodedDimension_eq]
  change Fintype.card Square ≤
    Module.finrank (ZMod 2) (LinearMap.ker D.chainComplex.boundary1) -
      Module.finrank (ZMod 2) (LinearMap.range D.chainComplex.boundary2) + _
  change Module.finrank (ZMod 2) (LinearMap.range D.chainComplex.boundary2) ≤
    Module.finrank (ZMod 2) (LinearMap.ker D.chainComplex.boundary1) at hBoundary
  rw [Nat.mul_add]
  omega
end QEC.Coding.QuantumTanner.Data
