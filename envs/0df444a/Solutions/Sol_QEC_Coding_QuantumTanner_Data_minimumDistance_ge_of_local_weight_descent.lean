-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.minimumDistance_ge_of_local_weight_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:08:50.548079+00:00
-- url     : https://prove2.me/submissions/9f25b4f3-bb82-4a0a-96d8-351007c5a434

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_hammingWeight_add_localExtension_lt_iff
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_localExtension_mem_firstCoboundaryCheckCode
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_localExtension_mem_middleBoundaryCode
import Theorems.Thm_QEC_Coding_algebraicCSSMinimumDistance_ge_of_add_weight_descent


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (D : Data G A B Square XBasis ZBasis) (threshold : Nat)
    (hreduceX : ∀ x : Word (ZMod 2) Square,
      x ∈ D.chainComplex.middleBoundaryCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B),
        c ∈ (tensorCode D.codeA.dual D.codeB.dual).carrier ∧
        HammingWeight (D.complex.localRestriction (g, true) x + c) <
          HammingWeight (D.complex.localRestriction (g, true) x))
    (hreduceZ : ∀ x : Word (ZMod 2) Square,
      x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B),
        c ∈ (tensorCode D.codeA D.codeB).carrier ∧
        HammingWeight (D.complex.localRestriction (g, false) x + c) <
          HammingWeight (D.complex.localRestriction (g, false) x))
    {distance : Nat}
    (hmin : AlgebraicCSSMinimumDistance D.chainComplex.firstCoboundaryCheckCode
      D.chainComplex.middleBoundaryCode distance) : threshold ≤ distance := by
  apply algebraicCSSMinimumDistance_ge_of_add_weight_descent
    D.chainComplex.firstCoboundaryCheckCode D.chainComplex.middleBoundaryCode
    D.chainComplex.firstCoboundaryCheckCode_le_middleBoundaryCode_dual
    D.chainComplex.middleBoundaryCode_le_firstCoboundaryCheckCode_dual threshold
    ?_ ?_ hmin
  · intro x hx hne hsmall
    obtain ⟨g, c, hc, hdecrease⟩ := hreduceX x hx hne hsmall
    exact ⟨D.complex.localExtension (g, true) c,
      D.localExtension_mem_firstCoboundaryCheckCode g c hc,
      (D.complex.hammingWeight_add_localExtension_lt_iff (g, true) x c).2 hdecrease⟩
  · intro x hx hne hsmall
    obtain ⟨g, c, hc, hdecrease⟩ := hreduceZ x hx hne hsmall
    exact ⟨D.complex.localExtension (g, false) c,
      D.localExtension_mem_middleBoundaryCode g c hc,
      (D.complex.hammingWeight_add_localExtension_lt_iff (g, false) x c).2 hdecrease⟩
end QEC.Coding.QuantumTanner.Data
