-- Prove2me | solution 1 for QEC.Semantics.Qudit.dimensions_positive_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:35.689662+00:00
-- url     : https://prove2.me/submissions/683229f0-5735-4871-a100-18655ca88ae1

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_DensityOperator_finrank_pos
import Theorems.Thm_QEC_Semantics_Qudit_finrank_quditRegister_eq_prod_dimensions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.Qudit
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Qudit
theorem _root_.solution (q : ι -> Nat)
    (rho : DensityOperator (QuditRegister q)) :
    forall i, 0 < q i := by
  have hproduct : 0 < ∏ i, q i := by
    rw [← finrank_quditRegister_eq_prod_dimensions]
    exact rho.finrank_pos
  intro i
  exact Nat.pos_of_ne_zero ((Finset.prod_ne_zero_iff.mp (Nat.ne_of_gt hproduct)) i
    (Finset.mem_univ _))
end QEC.Semantics.Qudit
