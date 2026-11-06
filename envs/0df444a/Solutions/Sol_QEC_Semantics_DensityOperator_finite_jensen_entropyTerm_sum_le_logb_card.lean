-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.finite_jensen_entropyTerm_sum_le_logb_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:30:05.106188+00:00
-- url     : https://prove2.me/submissions/7406b1ec-d774-404e-9c92-8a7ac300d613

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_DensityOperator_entropyTerm_sum_le_card_mul_entropyTerm_reciprocal
import Theorems.Thm_QEC_Semantics_DensityOperator_card_mul_entropyTerm_reciprocal_eq_logb

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (n : Nat) (hn : 0 < n)
    (p : Fin n -> Real) (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (∑ i, entropyTerm (p i)) <= Real.logb 2 (n : Real) := by
  calc
    (∑ i, entropyTerm (p i)) <= (n : Real) * entropyTerm ((n : Real)⁻¹) :=
      entropyTerm_sum_le_card_mul_entropyTerm_reciprocal n hn p hp hsum
    _ = Real.logb 2 (n : Real) := card_mul_entropyTerm_reciprocal_eq_logb n hn
end QEC.Semantics.DensityOperator
