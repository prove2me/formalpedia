-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.card_mul_entropyTerm_reciprocal_eq_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:29:34.632197+00:00
-- url     : https://prove2.me/submissions/19d24e76-bf7b-4575-909e-84151e73d09c

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds

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
theorem _root_.solution (n : Nat) (hn : 0 < n) :
    (n : Real) * entropyTerm ((n : Real)⁻¹) = Real.logb 2 (n : Real) := by
  rw [entropyTerm, if_neg (inv_ne_zero (by exact_mod_cast hn.ne')), Real.logb_inv]
  field_simp
end QEC.Semantics.DensityOperator
